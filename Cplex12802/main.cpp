#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list
#include <boost/graph/graphml.hpp>
#include <boost/graph/connected_components.hpp>
#include <ilcplex/ilocplex.h>
#include <boost/pending/disjoint_sets.hpp>
#include <boost/graph/incremental_components.hpp>
#include <boost/graph/copy.hpp>
#include <boost/dynamic_bitset.hpp>
#include <boost/program_options.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/trim.hpp>
#include <boost/graph/filtered_graph.hpp>
#include <boost/random/mersenne_twister.hpp>
#include <boost/random/uniform_int_distribution.hpp>
#include <boost/exception/all.hpp>
#include <exception>
#include <vector>
ILOSTLBEGIN //initialization make vs work properly

using namespace boost;
namespace po = boost::program_options;
//basic definitions
typedef IloArray<IloNumVarArray> IloVarMatrix;


typedef dynamic_bitset<> db;
typedef std::map<int, std::size_t> rank_t; // => order on Element
typedef std::map<int, int> parent_t;

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
template<class Graph, class Mask>
int get_components(Graph &g, Mask &m, vector<int> &components) {
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef typename boost::dynamic_bitset<> db;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	valid_edge_color<EdgeColorMap, Mask> filter(get(edge_color, g), m);
	fg tg(g, filter);
	int num = connected_components(tg, &components[0]);
	return num;
}

//MVCA modified always has k colors
template <class Graph>
int kLSFMVCA(Graph &g, int k_sup, int n_labels) {
	std::vector<int> components(num_vertices(g));
	db temp(n_labels);
	int f_colors = n_labels - num_vertices(g) + 1;
	int num_c = get_components(g, temp, components);
	int num_c_best = num_c;
	while (temp.count() < k_sup) {
		int best_label = 0;
		for (int i = 0; i < f_colors; ++i) {
			if (!temp.test(i)) {
				temp.set(i);
				int nc = get_components(g, temp, components);
				if (nc <= num_c_best) {
					num_c_best = nc;
					best_label = i;
				}
				temp.flip(i);
			}
		}
		temp.set(best_label);
	}
	num_c_best = get_components(g, temp, components);
	//print_filtered_graph(g,temp);
	return  num_c_best;//just to be right
}

template <class Graph>
db MkLSFMVCA(Graph &g, int k_sup, int n_labels) {
	std::vector<int> components(num_vertices(g));
	int f_colors = size - num_vertices(g) + 1;
	db temp(n_labels);
	int num_c = get_components(g, temp, components);
	int num_c_best = num_c;
	while (temp.count() < k_sup) {
		int best_label = 0;
		for (int i = 0; i < f_colors; ++i) {
			if (!temp.test(i)) {
				temp.set(i);
				int nc = get_components(g, temp, components);
				if (nc <= num_c_best) {
					num_c_best = nc;
					best_label = i;
				}
				temp.flip(i);
			}
		}
		temp.set(best_label);
	}
	//num_c_best = get_components(g, temp, components);
	//print_filtered_graph(g,temp);
	return  temp;//just to be right
}

int root(int current, std::vector<int> &parent) {
	while (parent[current] != current) {
		current = parent[current];
	}
	return current;
}

template<class Graph>
int max_reduce(Graph &g, int n_curr, int n_colors, std::vector<int> &comp, int label) {
	std::vector<int> parent(n_curr), level(n_curr);
	volatile int comp_a, comp_b; //so i could debug dont know why.
	int result;
	for (int i = 0; i < n_curr; ++i) {
		parent[i] = i;
		level[i] = 0;
	}
	result = 0;

	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	typedef typename fg::edge_iterator eit;
	eit it, end;
	db mask(n_colors);
	mask.set(label);
	valid_edge_color<EdgeColorMap, db> filter(get(edge_color, g), mask);
	fg G(g, filter);
	std::tie(it, end) = boost::edges(G);

	while (it != end) {
		comp_a = comp[source(*it, G)];
		comp_b = comp[target(*it, G)];
		if (comp_a != comp_b) {
			volatile int root_a, root_b;
			root_a = root(comp_a, parent);
			root_b = root(comp_b, parent);
			if (root(comp_a, parent) != root(comp_b, parent)) {
				if (level[root(comp_a, parent)] > level[root(comp_b, parent)]) parent[root(comp_b, parent)] = root(comp_a, parent);
				else {
					if (level[root(comp_a, parent)] == level[root(comp_b, parent)]) {
						level[root(comp_b, parent)]++;
					}
					parent[root(comp_a, parent)] = root(comp_b, parent);
				}
				result++;
			}
		}
		++it;
	}
	return result;
}

typedef typename adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> graph_t;

template<class Graph>
property_map<graph_t, edge_color_t>::type get_colors(Graph &g) {
	typedef typename property_map<Graph, edge_color_t>::type ColorMap;
	ColorMap colors = get(edge_color, g);
	//make color type generic
	return colors;
}

template<class Graph,class Model,class Mask>
void generateCuts(Graph g, Model &mod,Mask temp,int n_colors,IloBoolVarArray& z) {
	std::vector<int> components(num_vertices(g));
	auto colors = get_colors(g);
	graph_traits<graph_t>::edge_iterator it, end;
	//std::cout << " user cutting" << std::endl;
	int no = get_components(g, temp, components);
	int num_c_best = no;
	int best_label = -1;
	boost::random::mt19937 gen(std::time(0));
	boost::random::uniform_int_distribution<> dist(3, 10);
	int i = dist(gen);
	while (num_c_best >= i) {//peharps temp.count() < k_sup
														   /*boost::random::uniform_int_distribution<> gen(0, size-1);
														   int i = gen(rng);													   if (!temp.test(i))temp.set(i);
														   */
		int diff;
		int best_diff = num_vertices(g);
		no = num_c_best;
		best_label = -1;
		for (int i = 0; i < n_colors; ++i) {
			if (!temp.test(i)) {
				temp.set(i);
				num_c_best = get_components(g, temp, components);
				diff = no - num_c_best;
				if (diff < best_diff) {
					best_diff = diff;
					best_label = i;
					temp.flip(i);
					break;
				}
				temp.flip(i);
			}
		}
		if (best_label >= 0)temp.set(best_label);
		num_c_best = get_components(g, temp, components);
	}
	if (best_label >= 0)temp.flip(best_label);
	num_c_best = get_components(g, temp, components);
	if (num_c_best > 1) {
		//std::cout << "add user cut" << std::endl;
		//db temp1(size);
		std::tie(it, end) = edges(g);
		IloExpr expr(mod.getEnv());
		vector<db> masks(num_c_best);
		for (int i = 0; i < num_c_best; ++i) masks[i].resize(n_colors);
		while (it != end) {
			if (components[source(*it, g)] != components[target(*it, g)]) {
				masks[components[source(*it, g)]].set(colors[*it]);
				masks[components[target(*it, g)]].set(colors[*it]);
			}
			++it;
		}
		for (int i = 0; i < num_c_best; ++i) {
			for (int j = 0; j < n_colors; ++j) if (masks[i].test(j))expr += z[j];
			mod.add(expr >= 1);
			expr.clear();
		}
		expr.end();
	}


}



// preprocessing functions
template<class Graph>
void treefy(Graph& g, int n_colors) {
	Graph result(num_vertices(g));
	typedef boost::graph_traits<Graph>::edge_descriptor edge_t;
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	typedef typename fg::edge_iterator eit;
	eit it, end;
	for (int l = 0; l < n_colors; ++l) {
		db mask(n_colors);
		mask.set(l);
		std::vector<int> components(num_vertices(g));// components graph
		int n_curr = get_components(g, mask, components);
		std::vector<int> my_mapping(n_curr, -1);
		for (int u = 0; u < num_vertices(g); ++u) {
			if (my_mapping[components[u]] == -1)my_mapping[components[u]] = u;
			else add_edge(my_mapping[components[u]], u, property<edge_color_t, int>(l), result);
		}
	}
	g.clear();
	copy_graph(result, g);
}
template<class Graph>
void completefy(Graph& g, int n_colors) {
	Graph result(num_vertices(g));
	typedef boost::graph_traits<Graph>::edge_descriptor edge_t;
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	typedef typename fg::edge_iterator eit;
	eit it, end;
	for (int l = 0; l < n_colors; ++l) {
		db mask(n_colors);
		mask.set(l);
		std::vector<int> components(num_vertices(g));// components graph
		int n_curr = get_components(g, mask, components);
		std::vector<int> my_mapping(n_curr, -1);
		for (int u = 0; u < num_vertices(g); ++u) {
			for (int v = u + 1; v < num_vertices(g); ++v) {
				if (components[u] == components[v]) {
					add_edge(u, v, property<edge_color_t, int>(l), result);
				}
			}
		}
	}
	g.clear();
	copy_graph(result, g);
}
// preprocessing functions
template<class Graph>
void MCR(Graph& g, int n_colors) {
	Graph result(num_vertices(g));
	typedef boost::graph_traits<Graph>::edge_descriptor edge_t;
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	typedef typename fg::edge_iterator eit;
	eit it, end;
	for (int l = 0; l < n_colors; ++l) {
		db mask(n_colors);
		mask.set(l);
		valid_edge_color<EdgeColorMap, db> filter(get(edge_color, g), mask);
		fg H(g, filter);
		typedef typename property_map<fg, vertex_index_t>::type IndexMap;
		IndexMap index = get(vertex_index, H);
		//disjoint_sets ds(num_vertices(g))
	
		rank_t rank_map;
		parent_t parent_map;
		boost::associative_property_map<rank_t>   rank_pmap(rank_map);
		boost::associative_property_map<parent_t> parent_pmap(parent_map);
		boost::disjoint_sets<
			associative_property_map<rank_t>,
			associative_property_map<parent_t> > ds(
				rank_pmap,
				parent_pmap);
		//std::vector<Element> elements;
		//elements.push_back(Element(...));
		//rank_t rank_map;
		//parent_t parent_map;

		//boost::associative_property_map<rank_t>   rank_pmap(rank_map);
		//boost::associative_property_map<parent_t> parent_pmap(parent_map);

		for (int i = 0; i < num_vertices(g); ++i) {
			ds.make_set(i);
		}
		std::tie(it, end) = edges(H);
		while (it != end) {
			int u = index[source(*it, H)];
			int v = index[target(*it, H)];
			if (ds.find_set(u) != ds.find_set(v)) {
				add_edge(u, v, property<edge_color_t, int>(l), result);
				ds.union_set(u, v);
			}
			else {
				std::cout << "MCR removed edge:" << " (" << u << "," << v << ") " << " Color: " << l << std::endl;
			}
			++it;
		}
	}
	g.clear();
	copy_graph(result, g);
}


template<class Graph> // dont work with multigraph
void buildFlowModel(IloModel mod, IloBoolVarArray Z, IloVarMatrix F, const int k, const Graph &g,int opt) {
	IloEnv env = mod.getEnv();
	int n_colors = Z.getSize();
	typedef typename property_map<Graph, edge_color_t>::const_type ColorMap;
	typedef typename graph_traits<Graph>::edge_descriptor edge_desc;
	ColorMap colors = get(edge_color, g);
	/*std::vector<Graph> monocromatic_graphs(n_colors, Graph(num_vertices(g)));
	//creating new colored graphs mantain diferent colors
	auto[it_edges, last_edge] = edges(g);
	ColorMap colors = get(edge_color, g);
	while (it_edges != last_edge) {
		add_edge(source(*it_edges, g), target(*it_edges, g), property<edge_color_t, int>(colors[*it_edges]), monocromatic_graphs[colors[*it_edges]]);
		it_edges++;
	}*/

	//modelling objective function
	IloExpr exp(env);
	int n_vertices = num_vertices(g);
	int s = n_vertices - 1;//super source
	int f_colors = n_colors - n_vertices + 1;
	for (int i = f_colors; i < n_colors; ++i) {
		exp += Z[i];
	}
	mod.add(IloMinimize(env, exp));
	//mod.add(exp>=40);
	//mod.add(exp == 1);
	//exp.end();
	//modelling f_{ij} temporario ajeitar para deixar mais compactor depois um para cada aresta

	for (int i = 0; i < n_vertices; ++i) {
		F[i] = IloNumVarArray(env, n_vertices, 0, n_vertices-1, ILOFLOAT);
	}
	for (int i = 0; i < n_vertices; ++i) {
		for (int j = 0; j < n_vertices; ++j) {
			F[i][j].setName(("f_" + std::to_string(i) + "_" + std::to_string(j)).c_str());
		}
	}
	//setting names to labels variables.
	for (int i = 0; i<n_colors; ++i) {
		Z[i].setName(("z" + std::to_string(i)).c_str());
	}
	// first constraint
	typedef typename graph_traits<Graph>::vertex_iterator vertex_it;
	typedef typename graph_traits<Graph>::in_edge_iterator in_edge_it;
	IloExpr lhs(env);
	vertex_it vit, vend;
	std::tie(vit, vend) = vertices(g);
	in_edge_it eit, eend;
	for (auto it = vit; it != vend && *it<s; ++it) {
		std::tie(eit, eend) = in_edges(*it, g);
		for (auto tit = eit; tit != eend; ++tit) {
			lhs += F[source(*tit, g)][target(*tit, g)];
			//new constraint 1
			if (source(*tit, g) != s) {
				lhs -= F[target(*tit, g)][source(*tit, g)];
			}
		}
		//if(index[*it]%10==0) mod.add(texp == 1);
		//else mod.add(texp == 0);
		mod.add(lhs == 1);
		lhs.clear();
	}
	lhs.end();


	edge_desc my_edge;
	bool result = false;
	//IloExpr expression1(env);
	for (int i = 0; i < n_vertices-1; ++i) {
		for (int j = 0; j < n_vertices-1; ++j) {
			std::tie(my_edge, result) = edge(i, j, g);
			if (result) {
				mod.add(F[i][j]<= (n_vertices - 1) * Z[colors[my_edge]]);
				//mod.add(F[i][j] + exp <= (n_vertices));
				//expression1 += F[j][i];
				//mod.add(IloIfThen(env, Z[colors[my_edge]] == 0, F[j][i] + F[i][j] <= 0 ));
			}
		}
		/*for (int j = 0; j < n_vertices - 1; ++j) {
		std::tie(my_edge, result) = edge(i, j, g);
			if (result) {
				mod.add(F[i][j] <= expression1 + F[s][i]);
				//mod.add(IloIfThen(env, Z[colors[my_edge]] == 0, F[j][i] + F[i][j] <= 0 ));
			}
		}
		expression1.clear();*/
	}
	//expression1.end();
	//third big-mconstraint
	for (int i = f_colors; i < n_colors; ++i) {
		mod.add(F[s][i - f_colors] <= (n_vertices-1)*Z[i]);
		//mod.add(F[s][i - f_colors] + exp <= (n_vertices));
		//mod.add(IloIfThen(env,Z[i] == 0, F[s][i - f_colors] <= 0));
	}
	exp.end();
	//new constraint 1
	// first constraint
	/*IloExpr lhsNew(env);
	std::tie(vit, vend) = vertices(g);

	for (auto it = vit; it != vend && *it != s; ++it) {
		std::tie(eit, eend) = in_edges(*it, g);
		for (auto tit = eit; tit != eend; ++tit) {
			if(source(*tit, g)!=s)lhsNew += F[source(*tit, g)][target(*tit, g)];
		}
		//if(index[*it]%10==0) mod.add(texp == 1);
		//else mod.add(texp == 0);
		int u = static_cast<int>(*it);
		mod.add(lhsNew <=(n_vertices-1)*(1-Z[f_colors+u]));
		lhsNew.clear();
	}
	lhsNew.end();
	*/
	/*IloExpr exptreecut(env);
	auto [it, end] = edges(g);
	while (it != end) {
		exptreecut += Z[colors[*it]];
		++it;
	}
	int N = num_vertices(g) - 1;
	mod.add(exptreecut >= N);
	exptreecut.end();*/
	//new constraint dominating colors
	//strange implementation make it better with contraction
	/*for (int i = 0; i < n_colors; ++i) {
		std::vector<int> comps(num_vertices(g));
		int num_comps = connected_components(monocromatic_graphs[i],&comps[0]);
		IloExpr domination_expr(env);
		for (int j = 0; j < n_colors; j++) {
			if (i != j) {
				bool rs = false;
				for (auto it = edges(monocromatic_graphs[j]).first; it != edges(monocromatic_graphs[j]).second;++it) {
					if (comps[source(*it, monocromatic_graphs[j])]!=comps[target(*it, monocromatic_graphs[j])]) {
						rs = true;
						break;
					}
				}
				if (!rs) domination_expr += Z[j];
			}	
		}
		mod.add(domination_expr<=0);
	}*/


	//constraint every vertex has a colored edge incident
	auto [first_vertex, last_vertex] = vertices(g);
	while (first_vertex != last_vertex) {
		db used_colors(n_colors);
		auto[first_edge, last_edge] = in_edges(*first_vertex,g);
		IloExpr expInEdges(env);
		while (first_edge != last_edge) {
			volatile int idx = colors[*first_edge];
			if (!used_colors.test_set(idx,1)) {
				expInEdges += Z[colors[*first_edge]];
			}
			first_edge++;
		}
		mod.add(expInEdges >= 1);
		expInEdges.end();
		first_vertex++;
	}
	//new constraint based in monocromatic graphs
	auto[it_edges1, last_edge1] = edges(g);
	//ColorMap colors = get(edge_color, g);
	//não fortalece
	/*while (it_edges1 != last_edge1) {
		if (colors[*it_edges1] < f_colors) {
			int u = colors[edge(s, target(*it_edges1, g), g).first];
			int v = colors[edge(s, source(*it_edges1, g), g).first];
			//mod.add(Z[u] + Z[v] + Z[colors[*it_edges1]] <= 2);
			//if (u < v)mod.add(Z[v] + Z[colors[*it_edges1]] <= 1);
			//else mod.add(Z[u] + Z[colors[*it_edges1]] <= 1);
		}
		it_edges1++;
	}*/
	//forth constraint
	IloExpr texp(env);
	for (int i = 0; i < f_colors; ++i) {
		texp += Z[i];
	}
	mod.add(texp <= k);
	texp.end();

}

template<class Graph>
void solveModel(int n_vertices, int n_colors, int k, Graph &g) {

	//starting cplex code part
	IloEnv   env; //environment
	try {
		IloModel model(env);
		IloBoolVarArray Z(env, n_colors);
		IloNumArray pri(env, n_colors);
		IloVarMatrix    F(env, n_vertices); //each edge has at least a edge to the supersource
		int opt = kLSFMVCA(g, k, n_colors) - 1;
		buildFlowModel(model, Z, F, k, g,opt);

		/*for (int c = 0; c < n_colors;c++) {
			db mask(n_colors);
			mask.set(c);
			generateCuts(g, model, mask, n_colors, Z);
		}*/
		IloCplex cplex(model);
		int f_colors = n_colors - num_vertices(g) + 1;
		//cplex.exportModel("kSLF_fluxo.lp"); // good to see if the model is correct
											//cross your fingers
		{//set priorities number edges by color.
			auto it = boost::edges(g).first;
			auto end = boost::edges(g).second;
			auto colormap = get(edge_color, g);
			while (it != end) {
				pri[colormap[*it]]++;
				++it;
			}
		}

		//trying to disable automatic cuts
		//cplex.setParam(IloCplex::Param::MIP::Limits::CutPasses,-1);
		cplex.setParam(IloCplex::Param::MIP::Tolerances::LowerCutoff, 40);
		cplex.setParam(IloCplex::Param::MIP::Tolerances::UpperCutoff, opt);
		cplex.setParam(IloCplex::Param::Threads, 4);
		//cplex.setParam(IloCplex::Param::MIP::Strategy::VariableSelect, 3);
		//cplex.setParam(IloCplex::Param::Preprocessing::Presolve, 0);
		//cplex.setParam(IloCplex::Param::MIP::Display, 5);
		//cplex.setParam(IloCplex::Param::Tune::Display, 3);
		//cplex.setParam(IloCplex::Param::Tune::TimeLimit, 1e3);
		//cplex.setParam(IloCplex::Param::Simplex::Display, 2);
		cplex.setParam(IloCplex::Param::Parallel, -1);
		cplex.setParam(IloCplex::Param::Emphasis::MIP, 1);
		cplex.setParam(IloCplex::Param::Benders::Strategy,3);
		//cplex.setParam(IloCplex::Param::MIP::Limits::Nodes, 1);
		//std::ofstream LogFile("LogFile.txt");
		//cplex.setOut(LogFile);
		//cplex.setParam(IloCplex::Param::MIP::Strategy::RINSHeur, 1);
		//cplex.use(MyBranchStrategy(env, Z, k, g));
		//cplex.use(LazyCallback(env, Z, k, g));
		//TODO add MIP start
		// add set limit time
		cplex.setParam(IloCplex::TiLim, 7300);
		//set priorities to colors with more edges.
		cplex.setPriorities(Z, pri);
		//cplex.use(MyNewCuts(env, Z, g));
		//cplex.tuneParam(IloCplex::Param::Benders::Strategy);
		cplex.solve();
		//cplex.exportModel("kSLF_fluxo_after_presolve.lp");
		cplex.out() << "solution status = " << cplex.getStatus() << endl;

		cplex.out() << endl;
		cplex.out() << "Number of components   = " << cplex.getObjValue() << endl;
		db temp(n_colors);
		cplex.out() << "color(s) solution:";
		for (int i = 0; i < f_colors; i++) {
			if (std::abs(cplex.getValue(Z[i]) - 1.0f) <= 1e-3)cplex.out() << " " << i;
		}
		cplex.out() << endl;
		cplex.out() << "root(s) solution:";
		//int f_colors = Z.getSize() - n_vertices + 1;
		for (int i = f_colors; i < n_colors; i++) {
			if (std::abs(cplex.getValue(Z[i]) - 1.0f) <= 1e-3)cplex.out() << " " << i - f_colors;
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
			if (vm.count("include-path"))ifn.open((vm["include-path"].as<string>() + vm["input-file"].as<string>()).c_str(), ifstream::in);
			else ifn.open(vm["input-file"].as<string>().c_str(), ifstream::in);
			if (!ifn.is_open()) {
				std::cout << "error opening file" << std::endl;
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
				//std::tie(it, end) = boost::edges(g);
				//print_edges(it, end, g);
				MCR(g, n_colors);
				//treefy(g, n_colors);
				//completefy(g, n_colors);
				//auto colors = get(edge_color, g);
				//dynamic_properties dp;
				//dp.property("Color", colors);
				//std::ofstream tmp("out.graphml");
				//write_graphml(tmp, g, dp, true);
				solveModel(n_vertices, n_colors, k, g);
			}
			else {
				std::cout << "file wrong name format." << std::endl;
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
		std::cout << boost::diagnostic_information(ex) << std::endl;
	}
	catch (std::exception &ex) {
		std::cout << ex.what();
		exit(EXIT_FAILURE);
	}

	return 0;
}


