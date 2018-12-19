#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list
#include <ilcplex/ilocplex.h>
ILOSTLBEGIN //initialization make vs work properly

using namespace boost;

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
void buildFlowModel(IloModel mod,IloBoolVarArray Y, IloBoolVarArray Z,IloNumArray2 F,const Graph &g) {
	IloEnv env = mod.getEnv();

	//modelling objective function
	IloExpr exp(env);
	int n_vertices = num_vertices(g);
	for (int i = 1; i < n_vertices;++i) {
		exp += Y[i];
	}
	mod.add(IloMinimize(env,exp ));
	exp.end();

	//modelling flow to grant conectivity


}


int main()
{
	enum {A,B,C,D,E,F,G,H};
	typedef adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> Graph;
	typedef std::pair<int, int> Edge;
	Graph::edge_iterator it, end;
	const int num_vertices = 14;
	const int k = 4;
	Edge edge_array[] = {
		Edge(1,2),  Edge(1,12), Edge(2,3),  Edge(3,4),
		Edge(4,5),  Edge(5,6),  Edge(5,8),  Edge(5,9),
		Edge(5,11), Edge(5,13), Edge(6,7),  Edge(7,8),
		Edge(8,9),  Edge(9,10), Edge(10,11),Edge(11,12),
		Edge(12,13),
	};
	const int num_edges = sizeof(edge_array) / sizeof(edge_array[0]);
	const int colors[] = {H,H,D,D,C,F,E,D,C,F,G,E,A,B,G,A,B};

	//adicionar arestas do vertice super source 


	Graph g(edge_array,edge_array+num_edges,colors,num_vertices);
	std::tie(it, end) = boost::edges(g);
	print_edges(it, end, g);
	//starting cplex code part

	IloEnv   env; //environment
	try {
		IloModel model(env);
		IloBoolVarArray Y(env,num_vertices),Z(env,13);
		IloNumArray2    F(env,num_vertices);
		for (int i = 0; i < num_vertices; ++i) { //ajeitar para o numero de arestas
			F[i] = IloNumArray(env,num_vertices,0,+IloInfinity);
		}
		buildFlowModel(model,Y,Z,F,g);
		IloCplex cplex(model);
		cplex.exportModel("kSLF_fluxo.lp");
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