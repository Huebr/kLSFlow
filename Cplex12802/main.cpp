#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list
#include <boost/graph/graphml.hpp>
#include <boost/graph/connected_components.hpp>
#include <ilcplex/ilocplex.h>
#include <boost/dynamic_bitset.hpp>
#include <boost/program_options.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/trim.hpp>
#include <boost/graph/filtered_graph.hpp>
#include <boost/exception/all.hpp>
#include <exception>
#include <vector>
ILOSTLBEGIN //initialization make vs work properly

using namespace boost;
namespace po = boost::program_options;
//basic definitions
typedef IloArray<IloNumVarArray> IloVarMatrix;


typedef dynamic_bitset<> db;

template <typename EdgeColorMap, typename ValidColorsMap>
struct valid_edge_color {
	valid_edge_color() { }
	valid_edge_color(EdgeColorMap color, ValidColorsMap v_colors) : m_color(color), v_map(v_colors) { }
	template <typename Edge>
	bool operator()(const Edge& e) const {
		return v_map.test(get(m_color, e));
	}
	EdgeColorMap m_color;
	ValidColorsMap v_map;
};



template<class Graph, class Mask>
void print_filtered_graph(Graph &g, Mask valid) { //pay atention to the position of the bits and the colors positions in array
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef typename boost::dynamic_bitset<> db;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;

	valid_edge_color<EdgeColorMap, Mask> filter(get(edge_color, g), valid);
	fg tg(g, filter);
	print_edges(edges(tg).first, edges(tg).second, tg);
}
																																//template function to print edges.
template<class EdgeIter, class Graph>
void print_edges(EdgeIter first, EdgeIter last, const Graph& G) {
	typedef typename property_map<Graph, edge_color_t>::const_type ColorMap;
	ColorMap colors = get(edge_color, G);
	//make color type generic
	//typedef typename property_traits<ColorMap>::value_type ColorType;
	//ColorType edge_color;
	for (auto it = first; it != last; ++it) {
		std::cout << "Edge: " << "(" << source(*it, G) << "," << target(*it, G) << ") " << " Color: " << colors[*it] << "\n";
		std::cout << "Edge: " << "(" << target(*it, G) << "," << source(*it, G) << ") " << " Color: " << colors[*it] << "\n";
	}
	std::cout << " Number of vertex: " << num_vertices(G) << std::endl;
	std::cout << " Number of edges: " << num_edges(G) << std::endl;
	std::vector<int> components(num_vertices(G));
	int num = connected_components(G, &components[0]);
	std::vector<int>::size_type i;
	std::cout << "Total number of components: " << num << std::endl;
	for (i = 0; i != components.size(); ++i)
		std::cout << "Vertex " << i << " is in component " << components[i] << std::endl;
	std::cout << std::endl;
}
template<class Graph>
void buildFlowModel(IloModel mod,IloBoolVarArray Y, IloBoolVarArray Z,IloVarMatrix F,const int k,const Graph &g) {
	IloEnv env = mod.getEnv();
	int n_colors = Z.getSize();
	typedef typename property_map<Graph, edge_color_t>::const_type ColorMap;
	ColorMap colors = get(edge_color, g);
	//modelling objective function
	IloExpr exp(env);
	int n_vertices = num_vertices(g);
	int s = n_vertices- 1;//super source
	for (int i = 0; i < s;++i) {
		exp += Y[i];
		Y[i].setName(("y" + std::to_string(i)).c_str());
	}
	Y[s].setName(("y" + std::to_string(s)).c_str());//super source
	mod.add(IloMinimize(env,exp));
	exp.end();
	//modelling f_{ij} temporario ajeitar para deixar mais compactor depois um para cada aresta

	for (int i = 0; i < n_vertices; ++i){
		F[i] = IloNumVarArray(env,n_vertices,0,+IloInfinity,ILOFLOAT);
	}
	for (int i = 0; i < n_vertices; ++i) {
		for (int j = 0; j < n_vertices; ++j) {
			F[i][j].setName(("f_" + std::to_string(i) + "_" + std::to_string(j)).c_str());
		}
	}
	//setting names to labels variables.
	for (int i = 0; i<n_colors; ++i) {
		Z[i].setName(("z"+std::to_string(i)).c_str());
	}


	//first constraint 
	for(int i =0; i<s ; ++i)mod.add(F[s][i] <= (n_vertices-1)*Y[i] );

	//second constraint
    typedef typename graph_traits<Graph>::vertex_iterator vertex_it;
	typedef typename graph_traits<Graph>::in_edge_iterator in_edge_it;
	typedef typename graph_traits<Graph>::edge_iterator edge_it;
	vertex_it vit, vend;
	std::tie(vit, vend) = vertices(g);
	for (auto it = vit; it != vend&&*it<s; ++it) {
		in_edge_it eit, eend;
		std::tie(eit,eend) = in_edges(*it, g);
		//cout << "Vertex: " << *it << endl;
		//cout << "Aresta(s): ";
		IloExpr texp(env);
		for (auto tit = eit; tit != eend; ++tit) {
			texp += F[source(*tit, g)][target(*tit, g)];
			//cout << *tit;
		}
		for (auto tit = eit; tit != eend; ++tit) {
			texp -= F[target(*tit, g)][source(*tit, g)];
			//cout << *tit;
		}
		mod.add(texp == 1);
		texp.end();
		//cout << endl;
	}
	//third constraint
	for (edge_it it = edges(g).first; it != edges(g).second; ++it) {
		mod.add(F[source(*it, g)][target(*it, g)] <= (n_vertices-1) * Z[colors[*it]]);
		mod.add(F[target(*it, g)][source(*it, g)] <= (n_vertices-1) * Z[colors[*it]]);
	}

	//forth constraint
	int f_colors = n_colors - n_vertices+1;
	IloExpr texp(env);
	for (int i = 0; i < f_colors; ++i) {
		texp += Z[i];
	}
	mod.add(texp <= k);
	texp.end();

}

template<class Graph>
void solveModel(int n_vertices,int n_colors,int k,Graph &g) {

	//starting cplex code part
	IloEnv   env; //environment
	try {
		IloModel model(env);
		IloBoolVarArray Y(env, n_vertices), Z(env, n_colors);
		IloVarMatrix    F(env, n_vertices); //each edge has at least a edge to the supersource
		buildFlowModel(model, Y, Z, F, k, g);
		IloCplex cplex(model);
		cplex.exportModel("kSLF_fluxo.lp"); // good to see if the model is correct
											//cross your fingers
		cplex.solve();
		cplex.out() << "solution status = " << cplex.getStatus() << endl;

		cplex.out() << endl;
		cplex.out() << "Number of components   = " << cplex.getObjValue() << endl;
		db temp(n_colors);
		cplex.out() << "color(s) solution:";
		for (int i = 0; i < Z.getSize() - n_vertices + 1; i++) {
			if (cplex.getValue(Z[i]))cplex.out() << " " << i;
		}
		cplex.out() << endl;
		cplex.out() << "root(s) solution:";
		for (int i = 0; i < Y.getSize() - 1; i++) {
			if (cplex.getValue(Y[i]))cplex.out() << " " << i;
		}
		cplex.out() << endl;

	}
	catch (IloException& e) {
		cerr << "Concert exception caught: " << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught" << endl;
	}
	//memory cleaning
	env.end();
}


int main(int argc, const char *argv[])
{
	typedef adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> Graph;
	typedef std::pair<int, int> Edge;
	typedef boost::graph_traits<Graph>::vertex_descriptor vertex_t;
	Graph::edge_iterator it, end;
	Graph g;
	int n_vertices, n_colors;
	//command-line processor

	try {
		std::ifstream ifn;
		po::options_description desc{ "Options" };
		desc.add_options()("help,h", "produce help message")
			("input-file,i", po::value< string >(), "input file")
			("include-path,I", po::value< string >(), "include path")
			("setup-file", po::value< string >(), "setup file");
		po::positional_options_description p;
		p.add("input-file", -1);


		po::variables_map vm;
		po::store(po::command_line_parser(argc, argv).
			options(desc).positional(p).run(), vm);
		po::notify(vm);

		if (vm.count("help")) {
				cout << desc << "\n";
				return 1;
		}
		else if (vm.count("input-file"))
		{
			std::cout << "Input files are: " << vm["input-file"].as<string>() << "\n";
			if (vm.count("include-path"))ifn.open((vm["include-path"].as<string>()+vm["input-file"].as<string>()).c_str(), ifstream::in);
			else ifn.open(vm["input-file"].as<string>().c_str(), ifstream::in);
			if (!ifn.is_open()) {
				std::cout << "error opening file"<<std::endl;
				exit(EXIT_FAILURE);
			}
			dynamic_properties dp;
			dp.property("color", get(edge_color, g));
			read_graphml(ifn, g, dp);

			vector<string> vecI;
			split(vecI, vm["input-file"].as<string>(), is_any_of("-."), token_compress_off);
			if (vecI.size() == 6) {
				std::cout << vecI[0] << std::endl;
				n_vertices = stoi(vecI[0]);
				std::cout << vecI[2] << std::endl;
				n_colors = stoi(vecI[2]);
				std::cout << vecI[3] << std::endl;
				int k = stoi(vecI[3]);
				//add edges to super source vertex. remember!!!
				vertex_t u = add_vertex(g);
				n_vertices++;
				for (int i = 0; i < n_vertices - 1; ++i) boost::add_edge(u, i, property<edge_color_t, int>(n_colors++), g);
				std::tie(it, end) = boost::edges(g);
				//print_edges(it, end, g);
				solveModel(n_vertices, n_colors, k, g);
			}
			else {
				std::cout << "file wrong name format."<<std::endl ;
			}
		
		}
		else if (vm.count("setup-file")) {
			std::cout << "Not implemented yet" << std::endl;
		}
		else {
			std::cout << "see options(-h)." << std::endl;
		}

		
	}
	catch (const po::error &ex) {
		std::cout << ex.what();
		exit(EXIT_FAILURE);
	}
	catch (boost::exception &ex) {
		std::cout << boost::diagnostic_information(ex)<<std::endl;
	}
	catch (std::exception &ex) {
		std::cout << ex.what();
		exit(EXIT_FAILURE);
	}

	return 0;
}