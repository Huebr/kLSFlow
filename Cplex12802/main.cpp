#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list
#include <ilcplex/ilocplex.h>
#include <unordered_set>
ILOSTLBEGIN //initialization make vs work properly

using namespace boost;

//basic definitions
typedef IloArray<IloNumVarArray> IloVarMatrix;


//template function to print edges.
template<class EdgeIter,class Graph>
void print_edges(EdgeIter first, EdgeIter last, const Graph& G) {
	typedef typename property_map<Graph, edge_color_t>::const_type ColorMap;
	ColorMap colors = get(edge_color, G);
	//make color type generic
	//typedef typename property_traits<ColorMap>::value_type ColorType;
	//ColorType edge_color;
	for (auto it = first; it != last;++it) {
		std::cout <<"Edge: "<< "(" << source(*it, G) << "," << target(*it, G) << ") " << " Color: " << colors[*it]<<"\n";
		std::cout << "Edge: " << "(" << target(*it, G) << "," << source(*it, G) << ") " << " Color: " << colors[*it] << "\n";
	}
	cout << " Number of vertex: " << num_vertices(G) << std::endl;
	cout << " Number of edges: " << num_edges(G) << std::endl;
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
	for (int i = 1; i < n_vertices;++i) {
		exp += Y[i];
		Y[i].setName(("y" + std::to_string(i)).c_str());
	}
	Y[0].setName("y0");
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
	for(int i =1; i<n_vertices ; ++i)mod.add(F[0][i] <= n_vertices*Y[i] );

	//second constraint
    typedef typename graph_traits<Graph>::vertex_iterator vertex_it;
	typedef typename graph_traits<Graph>::in_edge_iterator in_edge_it;
	typedef typename graph_traits<Graph>::edge_iterator edge_it;
	vertex_it vit, vend;
	std::tie(vit, vend) = vertices(g);
	for (auto it = ++vit; it != vend; ++it) {
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
		mod.add(F[source(*it, g)][target(*it, g)] <= n_vertices * Z[colors[*it]]);
		mod.add(F[target(*it, g)][source(*it, g)] <= n_vertices * Z[colors[*it]]);
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




int main()
{
	enum {A,B,C,D,E,F,G,H};
	typedef adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> Graph;
	typedef std::pair<int, int> Edge;
	Graph::edge_iterator it, end;
	const int n_vertices = 14;
	const int k = 4;
	Edge edge_array[] = {
		Edge(1,2),  Edge(1,12), Edge(2,3),  Edge(3,4),
		Edge(4,5),  Edge(5,6),  Edge(5,8),  Edge(5,9),
		Edge(5,11), Edge(5,13), Edge(6,7),  Edge(7,8),
		Edge(8,9),  Edge(9,10), Edge(10,11),Edge(11,12),
		Edge(12,13),
	};
	int n_edges = sizeof(edge_array) / sizeof(edge_array[0]);
	const int colors[] = {H,H,D,D,C,F,E,D,C,F,G,E,A,B,G,A,B};

	Graph g(edge_array,edge_array+n_edges,colors,n_vertices);
	//add edges to super source vertex index 0. remember!!!
	std::unordered_set<int> st(colors, colors + sizeof(colors) / sizeof(colors[0]));
	int n_colors = st.size();
	st.clear();
	for (int i = 1; i < n_vertices; ++i) boost::add_edge(0,i,property<edge_color_t,int>(n_colors+i-1),g);
	std::tie(it, end) = boost::edges(g);
	print_edges(it, end, g);


	//temporario contar numero de cores
	n_colors += n_vertices - 1;


	//starting cplex code part
	IloEnv   env; //environment
	try {
		IloModel model(env);
		IloBoolVarArray Y(env,n_vertices),Z(env,n_colors);
		IloVarMatrix    F(env,n_vertices); //each edge has at least a edge to the supersource
		buildFlowModel(model,Y,Z,F,k,g);
		IloCplex cplex(model);
		cplex.exportModel("kSLF_fluxo.lp"); // good to see if the model is correct
		//cross your fingers
		cplex.solve();
		cplex.out() << "solution status = " << cplex.getStatus() << endl;

		cplex.out() << endl;
		cplex.out() << "Number of components   = " << cplex.getObjValue() << endl;
		for (int i = 0; i <= Z.getSize() - n_vertices; i++) {
			cplex.out() << "  Z" << i << " = " << cplex.getValue(Z[i]) << endl;
		}

	}
	catch (IloException& e) {
		cerr << "Concert exception caught: " << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught" << endl;
	}
	//memory cleaning
	env.end(); 

	return 0;
}