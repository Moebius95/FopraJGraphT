import org.jgrapht.*;
import org.jgrapht.alg.StoerWagnerMinimumCut;
import org.jgrapht.alg.cycle.PatonCycleBase;
import org.jgrapht.alg.flow.EdmondsKarpMFImpl;
import org.jgrapht.alg.partition.BipartitePartitioning;
import org.jgrapht.graph.*;
import org.jgrapht.nio.*;
import org.jgrapht.nio.dot.DOTExporter;
import org.jgrapht.traverse.*;

import java.io.*;
import java.net.*;
import java.util.*;

public final class JGraphT
{
    private JGraphT()
    {
    }

    public static void main(String[] args)
            throws URISyntaxException,
            ExportException, IOException
    {

    }
    
    //returns true iff graph g is a cograph
    public static boolean isCograph(Graph<Integer, DefaultEdge> g) {
    	for(DefaultEdge e : g.edgeSet()) {
    		for(DefaultEdge f : g.edgeSet()) {
    			int a = g.getEdgeSource(e);
    			int b = g.getEdgeTarget(e);
    			int c = g.getEdgeSource(f);
    			int d = g.getEdgeTarget(f);
    			if(g.containsEdge(a,c) && !g.containsEdge(a,d) && !g.containsEdge(b,c) && !g.containsEdge(b,d)
    							|| g.containsEdge(a,d) && !g.containsEdge(a,c) && !g.containsEdge(b,c) && !g.containsEdge(b,d)
    							|| g.containsEdge(b,c) && !g.containsEdge(b,d) && !g.containsEdge(a,c) && !g.containsEdge(a,d)
    							|| g.containsEdge(b,d) && !g.containsEdge(b,c) && !g.containsEdge(a,c) && !g.containsEdge(a,d)){
    			return false;					
    			}
    		}
    	}
    	return true;
    }
    
    //returns k for a k-connected graph
    public static int kConnected(Graph<Integer, DefaultEdge> g) {
    	int k = g.vertexSet().size();
    	int s = (int) g.vertexSet().toArray()[0];
    	for (int t : g.vertexSet()) {
    		if (s == t) continue;
    		EdmondsKarpMFImpl<Integer, DefaultEdge> mCut = new EdmondsKarpMFImpl<Integer, DefaultEdge>(g);
    		int l = (int) mCut.calculateMinCut(s, t);
    		if (l < k) k = l;
    	}
    	return k;
    }
    
    //returns true iff graph g is a cactus graph
    public static boolean isCactusGraph(Graph<Integer, DefaultEdge> g) {
        PatonCycleBase<Integer, DefaultEdge> cycles = new PatonCycleBase<Integer, DefaultEdge>(g);
        for (DefaultEdge e : g.edgeSet()) {
        	int eCycles = 0;
	        for (List<DefaultEdge> l : cycles.getCycleBasis().getCycles()) {
	        	if (l.contains(e)) eCycles++;
	        	if (eCycles > 1) return false;
	        }
        }
        return true;
    }
    
    //returns true iff graph g is a bipartite chain graph
    public static boolean isBisplit(Graph<Integer, DefaultEdge> g) {
    	BipartitePartitioning<Integer, DefaultEdge> b = new BipartitePartitioning<Integer, DefaultEdge>(g);
    	if (b.isBipartite()) {
    		Set<Integer> uSet = b.getPartitioning().getPartition(0);
    		Set<Integer> vSet = b.getPartitioning().getPartition(1);
    		int[] uVertices = new int[uSet.size()];
    		int[] vVertices = new int[vSet.size()];
    		int i = 0;
    		for (int u : uSet) {
    			uVertices[i++] = u;
    		}
    		i = 0;
    		for (int v : vSet) {
    			vVertices[i++] = v;
    		}
    		for (int j = uVertices.length - 1; j > 1; --j) {
    			for (int k = 0; k < j - 1; ++k) {
    				if (Graphs.neighborListOf(g, uVertices[j]).size() > Graphs.neighborListOf(g, uVertices[k]).size()) {
    					int temp = uVertices[j];
    					uVertices[j] = uVertices[k];
    					uVertices[k] = temp;
    					continue;
    				}
    			}
    		}
    		
    		for (int j = vVertices.length - 1; j > 1; --j) {
    			for (int k = 0; k < j - 1; ++k) {
    				if (Graphs.neighborListOf(g, vVertices[j]).size() > Graphs.neighborListOf(g, vVertices[k]).size()) {
    					int temp = vVertices[j];
    					vVertices[j] = vVertices[k];
    					vVertices[k] = temp;
    					continue;
    				}
    			}
    		}
    		for (int j = 0; j < uVertices.length - 1; j++) {
    			if (!Graphs.neighborListOf(g, uVertices[j]).containsAll(Graphs.neighborListOf(g, uVertices[j + 1]))) return false;
    		}
    		for (int j = 0; j < vVertices.length - 1; j++) {
    			if (!Graphs.neighborListOf(g, vVertices[j]).containsAll(Graphs.neighborListOf(g, vVertices[j + 1]))) return false;
    		}
    		return true;
    	}
    	return false;
    }

    //returns true iff graph g is clawfree
    public static boolean isClawfree(Graph<Integer, DefaultEdge> g) {
    	for (int i : g.vertexSet()) {
    		List<Integer> gNeighbors = Graphs.neighborListOf(g, i);
    		for (int u : gNeighbors) {
    			for (int v : gNeighbors) {
    				for (int w : gNeighbors) {
    					if (u != v && v != w && u != w
    							&& !g.containsEdge(u, v) && !g.containsEdge(u, w) && !g.containsEdge(v, w)) {
    						return false;
    					}
    	    		}
    			}
    		}
    	}
    	return true;
    }
    
    //returns true iff graph g is a threshold graph
    public static boolean isThresholdgraph(Graph<Integer, DefaultEdge> g) {
    	int n = g.vertexSet().size();
    	int[] con = new int[n];
    	for(DefaultEdge e : g.edgeSet()) {
    		con[g.getEdgeSource(e) - 1]++;
    		con[g.getEdgeTarget(e) - 1]++;
    	}
    	Arrays.sort(con);
    	int l = 0;
    	int r = con.length - 1;
    	int domRem = 0;
    	int isoRem = 0;
    	while (con[l] == 0 ) {
    		con[l] = -1;
    		isoRem++;
    		l++;
    		if (l <= g.vertexSet().size()) break;
    	}
    	while(l != r) {
    		if (con[r] == n - isoRem - 1) {
    			con[r] = -1;
    			domRem++;
    			r--;
    		}
    		else if (con[l] == domRem) {
    	    	con[l] = -1;
    	    	isoRem++;
    	    	l++;
    		}
    		else {
    			return false;
    		}
    		
    	}
    	return true;
    }
	
	/**
	 * Implements paper for <a href="http://www.cs.uoi.gr/~palios/pubs/D5.pdf">hole free graph recognition</a>
	 * @param graph
	 * @return true if graph is a <a href="https://www.graphclasses.org/classes/gc_437.html">hole free graph </a>
	 */
	public static <V, E> boolean isHoleFree(Graph<V, E> graph) {
		HashMap<Triple<V, V, V>, Integer> not_in_hole = new HashMap<>();
		Integer[] in_path = new Integer[graph.vertexSet().size()];
		Arrays.fill(in_path, 0);
		ArrayList<ArrayList<V>> adjList = adjacencyMatrix(graph);
		ArrayList<V> vertices = new ArrayList<>(graph.vertexSet());
		for (int i = 0; i < in_path.length; i++) {
			V u = vertices.get(i);
			in_path[i] = 1;
			for (E e : graph.edgeSet()) {
				V v = graph.getEdgeSource(e);
				V w = graph.getEdgeTarget(e);
				if (!u.equals(v) && !u.equals(w)) {
					Triple<V, V, V> triple = new Triple<V, V, V>(u, v, w);
					if (!not_in_hole.containsKey(triple)) {
						not_in_hole.put(triple, 0);
					}
					if (adjList.get(vertices.indexOf(u)).contains(v) && !adjList.get(vertices.indexOf(u)).contains(w)
							&& not_in_hole.get(triple) == 0) {
						in_path[vertices.indexOf(v)] = 1;
						boolean hasHole = process(graph, not_in_hole, in_path, adjList, u, v, w);
						if (hasHole)
							return false;
						in_path[vertices.indexOf(v)] = 0;
					}
				}
			}
			in_path[vertices.indexOf(u)] = 0;
		}
		return true;
	}
	
	/**
	 * Implements paper for <a href="https://www.researchgate.net/publication/339503756_Recognition_and_Optimization_Algorithms_for_P5-Free_Graphs">p5 free graph recognition</a>
	 * @param graph
	 * @return true if graph is a <a href="https://www.graphclasses.org/classes/gc_396.html">p5 free graph</a>
	 */
	public static <V, E> boolean isGraphP5Free(Graph<V, E> graph) {
		List<Graph<V, E>> L = new ArrayList<>();
		L.add(graph);
		Graph<V, E> H = graph;
		while (H.vertexSet().size() > 5) {
			ListTriple<V, V, V> triple = weakDecomposition(H);
			List<V> A = triple.first;
			List<V> N = triple.first;
			List<V> R = triple.first;
			Set<V> B = new LinkedHashSet<V>();
			for (V v : H.vertexSet()) {
				if (N.contains(v)) {
					List<V> neighbors = Graphs.neighborListOf(H, v);
					B.addAll(neighbors);
				}
			}
			B.removeAll(R);
			List<V> C = new ArrayList<>();
			C.addAll(A);
			C.removeAll(B);
			Integer nr = N.size();
			Integer r = R.size();
			Integer b = B.size();
			for (V v : R) {
				if (H.degreeOf(v) != nr)
					return false;
			}
			for (V v : N) {
				if (H.degreeOf(v) != b + r)
					return false;
			}
			Graph<V, E> AGraph = new SimpleGraph<V, E>(H.getVertexSupplier(), H.getEdgeSupplier(), false);
			AGraph.vertexSet().addAll(A);
			for (V v : H.vertexSet()) {
				Set<E> edges = H.edgesOf(v);
				for (E e : edges) {
					if (A.contains(H.getEdgeSource(e)) && A.contains(H.getEdgeTarget(e))) {
						AGraph.addEdge(H.getEdgeSource(e), H.getEdgeTarget(e));
					}
				}
			}
			L.add(AGraph);
			H = AGraph;
		}
		return true;
	}
	
	/**
	 * Implements paper for <a href="https://www.researchgate.net/publication/266939196_Determination_of_permutation_graphs">permutation graph recognition</a>
	 * @param graph
	 * @return true if graph is a <a href="https://www.graphclasses.org/classes/gc_23.html">permutation graph</a>
	 */
	public static <V, E> boolean isPermutationGraph(Graph<V, E> graph) {
		List<List<V>> permutationList = getPermutation(graph, new ArrayList<>(graph.vertexSet()));
		List<V> vertices = new ArrayList<>(graph.vertexSet());
		Map<V,Integer> vertexMap = new HashMap<>();
		for (int i = 0; i < vertices.size(); i++) {
			vertexMap.put(vertices.get(i), i);
		}
		int x = 0;
		for (V sourceVertex : vertices) {
			for (List<V> vertexList : permutationList) {
				V vertex = vertexList.get(0);
				if (sourceVertex.equals(vertex)) {
					break;
				} else {
					if(vertexMap.get(vertex) > vertexMap.get(sourceVertex)) {
						if(!graph.containsEdge(sourceVertex, vertex)) {
							return false;
						}
						x++;
					}
				}
			}
		}
		return graph.edgeSet().size() == x;
	}
	
	/**
	 * Implements paper for <a href="https://ir.nctu.edu.tw/bitstream/11536/1095/1/A1996VD36900004.pdf">quasi-threshold graph recognition</a>
	 * @param graph
	 * @return true if graph is a <a href="https://www.graphclasses.org/classes/gc_781.html">quasi-threshold graph</a>
	 */
	public static <V, E> boolean isQuasiTreshHoldGraph(Graph<V, E> a) {
		HashMap<V, Triple<Integer, Integer, Integer>> degreeMap = new HashMap<>();
		Graph<V, E> diGraph = new DefaultDirectedGraph<>(a.getVertexSupplier(), a.getEdgeSupplier(), false);
		ArrayList<V> allV = new ArrayList<>(a.vertexSet());
		for (int i = 0; i < allV.size(); i++) {
			V vertex = allV.get(i);
			diGraph.addVertex(vertex);
			degreeMap.put(vertex, new Triple<Integer, Integer, Integer>(a.degreeOf(vertex), 0, 0));
		}
		Iterator<E> iterator = a.edgeSet().iterator();
		while (iterator.hasNext()) {
			E edge = iterator.next();
			V vi = a.getEdgeSource(edge);
			V vj = a.getEdgeTarget(edge);
			if ((a.degreeOf(vi) > a.degreeOf(vj))
					|| (a.degreeOf(vi) == a.degreeOf(vj) && allV.indexOf(vi) < allV.indexOf(vj))) {
				Triple<Integer, Integer, Integer> pair = degreeMap.get(vj);
				pair.setSecond(pair.getSecond() + 1);
			} else {
				Triple<Integer, Integer, Integer> pair = degreeMap.get(vi);
				pair.setSecond(pair.getSecond() + 1);
			}
		}
		for (int j = 0; j < allV.size(); j++) {
			V vj = allV.get(j);
			if (degreeMap.get(vj).getSecond() >= 1) {
				V vi = getSpecialVertex(allV, degreeMap, Graphs.neighborListOf(a, vj), vj);
				if (vi != null) {
					diGraph.addEdge(vi, vj);	
				}
			}
		}
		for (int j = 0; j < allV.size(); j++) {
			V vj = allV.get(j);
			int index = 0;
			while (!diGraph.incomingEdgesOf(vj).isEmpty()) {
				vj = diGraph.getEdgeSource(diGraph.incomingEdgesOf(vj).iterator().next());
				index++;
			}
			degreeMap.get(allV.get(j)).setThird(index);
		}
		for (int j = 0; j < allV.size(); j++) {
			Triple<Integer, Integer, Integer> triple = degreeMap.get(allV.get(j));
			if (triple.getSecond() != triple.getThird())
				return false;
		}
		return true;
	}
	
//_____________________________HELPER_FUNCTIONS_FOR_GRAPH_CREATION_______________________________________________________________________
    
    
    //returns a P4 graph
    private static Graph<Integer, DefaultEdge> createP4(int v1, int v2, int v3, int v4)
    {
        Graph<Integer, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
        g.addVertex(v1);
        g.addVertex(v2);
        g.addVertex(v3);
        g.addVertex(v4);
        //connects four vertices resulting in a P4 graph
        g.addEdge(v1, v2);
        g.addEdge(v2, v3);
        g.addEdge(v3, v4);

        return g;
    }
    
    //returns a P3 graph
    private static Graph<Integer, DefaultEdge> createP3(int v1, int v2, int v3)
    {
        Graph<Integer, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
        g.addVertex(v1);
        g.addVertex(v2);
        g.addVertex(v3);
        //connects three vertices resulting in a P3 graph
        g.addEdge(v1, v2);
        g.addEdge(v2, v3);

        return g;
    }
    
    //returns the disjoint union of two graphs
    public static Graph<Integer, DefaultEdge> 
    		disjointUnion(Graph<Integer, DefaultEdge> g, Graph<Integer, DefaultEdge> h) {
    	Graph<Integer, DefaultEdge> gh = new SimpleGraph<>(DefaultEdge.class);
    	//adds all vertices from both graphs to new graph
    	for(int u : g.vertexSet()) {
    		gh.addVertex(u);
    	}
    	for(int v : h.vertexSet()) {
    		gh.addVertex(v);
    	}
    	//adds all edges from both graphs to new graph
    	for(DefaultEdge e : g.edgeSet()) {
    		gh.addEdge(g.getEdgeSource(e), g.getEdgeTarget(e));
    	}
    	for(DefaultEdge e : h.edgeSet()) {
    		gh.addEdge(h.getEdgeSource(e), h.getEdgeTarget(e));
    	}
    	return gh;
    }
    

    //creates a new graph from two graphs where every vertex
    //from graph g is connected to every vertex from graph h and vice versa
    public static Graph<Integer, DefaultEdge> 
			allToAllConnect (Graph<Integer, DefaultEdge> g, Graph<Integer, DefaultEdge> h) {
    	Graph<Integer, DefaultEdge> gh = new SimpleGraph<>(DefaultEdge.class);
    	gh = disjointUnion(g, h);
    	for (int u : g.vertexSet()) {
    		for (int v: h.vertexSet()) {
    			gh.addEdge(u, v);
    		}
    	}
    	return gh;
    }
    
    public static Graph<Integer, DefaultEdge> claw (int v1, int v2, int v3, int v4) {
     	Graph<Integer, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
     	g.addVertex(v1);
     	g.addVertex(v2);
     	g.addVertex(v3);
     	g.addVertex(v4);
     	g.addEdge(v1, v2);
     	g.addEdge(v1, v3);
     	g.addEdge(v1, v4);
     	return g;
     }
    
    
    //inverts a graph
    public static void invertGraph(Graph<Integer, DefaultEdge> g) {
    	for(int u : g.vertexSet()) {
    		for(int v : g.vertexSet()) {
    			if (u < v) {
    				if (g.containsEdge(u, v)) g.removeEdge(u, v);
    				else g.addEdge(u, v);
    			}
    		}
    	}
    }

    // creates a graph with n vertices that are all connected to each other
    public static Graph<Integer, DefaultEdge> allConnected(int start, int n) {
    	Graph<Integer, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
    	for (int i = 1; i <= n; i++) {
    		g.addVertex(start + i - 1);
    	}
    	for (int u : g.vertexSet()) {
    		for (int v : g.vertexSet()) {
    			if (u < v) {
    	    		g.addEdge(u, v);
    			}
    		}
    	}
    	return g;
    }
    
    public static DefaultDirectedGraph<Integer, DefaultEdge> makeDirected (Graph<Integer, DefaultEdge> g) {
    	DefaultDirectedGraph<Integer, DefaultEdge> h = new DefaultDirectedGraph<>(DefaultEdge.class);
    	for (int v : g.vertexSet()) {
    		h.addVertex(v);
    	}
    	for (DefaultEdge e : g.edgeSet()) {
    		h.addEdge(g.getEdgeSource(e), g.getEdgeTarget(e));
    		h.addEdge(g.getEdgeTarget(e), g.getEdgeSource(e));
    	}
    	return h;
    }
    
    public static Graph<Integer, DefaultEdge> circleGraph(int start, int n) {
    	Graph<Integer, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
    	for (int i = 0; i < n; i++) {
    		g.addVertex(start + i);
    	}
    	for (int i = 0; i < n - 1; i++) {
    		g.addEdge(start + i, start + i + 1);
    	}
    	g.addEdge(start, start + n - 1);
    	return g;
    }

    public static Graph<Integer, DefaultEdge> cactusWorstCase(int n) {
    	Graph<Integer, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
    	g.addVertex(1);
    	for (int i = 2; i < n; i+=2) {
    		g.addVertex(i);
    		g.addVertex(i + 1);
    		g.addEdge(1, i);
    		g.addEdge(1, i + 1);
    		g.addEdge(i, i + 1);
    	}
    	return g;
    }
    
    public static Graph<Integer, DefaultEdge> bisplitWorstCase(int n) {
    	Graph<Integer, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
    	Graph<Integer, DefaultEdge> h = new SimpleGraph<>(DefaultEdge.class);
    	for (int i = 1; i <= n; i++) {
    		g.addVertex(i);
    		h.addVertex(n + i);
    	}
    	g = allToAllConnect(g, h);
    	return g;
    }
    
    public static Graph<Integer, DefaultEdge> thresholdWorstCase(int n) {
    	Graph<Integer, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
    	for (int i = 1; i <= n; i++) {
    		g.addVertex(i);
    	}
    	return g;
    }
    public static Graph<Integer, DefaultEdge> thresholdWorstCase2(int n) {
    	Graph<Integer, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
    	for (int i = 1; i <= n; i++) {
    		g.addVertex(i);
    		for (int u : g.vertexSet()) {
    			if (i != u) g.addEdge(u, i);
    		}
    	}
    	return g;
    }
    
    //saves graph to file in standard JGraphT format
    public static void saveGraph(Graph<Integer, DefaultEdge> g, String fileName) throws IOException {
        String graph = g.toString();
        PrintWriter out = new PrintWriter(fileName);
        out.println(graph);
        out.close();
    }
    
    
    
    //reads a graph from a txt-file
    public static Graph<Integer, DefaultEdge> txtToGraph(String fileName) {
    	Graph<Integer, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
    	try {
    	      File myObj = new File(fileName);
    	      Scanner myReader = new Scanner(myObj);
    	      while (myReader.hasNextLine()) {
    	        String data = myReader.nextLine();
    	        data = data.replaceAll("\\[", "");
    	        data = data.replaceAll("\\(", "");
    	        String vertices[] = data.split("\\]")[0].split(",");
    	        for (String vert : vertices) {
    	        	g.addVertex(Integer.parseInt(vert.trim()));
    	        }
    	        String edges[] = data.split("]")[1].replaceAll("\\s+", "").replaceAll("\\}", "").split("\\{");
    	        for(int i = 1; i < edges.length; i++) {
        	        int j = Integer.parseInt(edges[i].split(",")[0]);
        	        int k = Integer.parseInt(edges[i].split(",")[1]);
        	        g.addEdge(j, k);
    	        }
    	      }
    	      myReader.close();
    	    } catch (FileNotFoundException e) {
    	      System.out.println("An error occurred.");
    	      e.printStackTrace();
    	    }
    	return g;
    }
	
	// builds a adjacency matrix 
	@SuppressWarnings("unchecked")
	private static <V, E> ArrayList<ArrayList<V>> adjacencyMatrix(Graph<V, E> graph) {
		int totalVertices = graph.vertexSet().size();
		Map<V, Integer> vertexIndexMap = new HashMap<>();
		V[] vertexMap = (V[]) new Object[totalVertices];
		int[] outDegree = new int[totalVertices];

		int i = 0;
		for (V v : graph.vertexSet()) {
			vertexIndexMap.put(v, i);
			vertexMap[i] = v;
			outDegree[i] = graph.outDegreeOf(v);
			i++;
		}
		ArrayList<ArrayList<V>> adjList = new ArrayList<>(totalVertices);
		for (i = 0; i < totalVertices; i++) {
			V v = vertexMap[i];
			ArrayList<V> inNeighbors = new ArrayList<>();
			for (E e : graph.incomingEdgesOf(v)) {
				V w = Graphs.getOppositeVertex(graph, e, v);
				inNeighbors.add(w);
			}
			adjList.add(inNeighbors);
		}
		return adjList;
	}
	
	// needed for hole free graph recognition
	private static <V, E> boolean process(Graph<V, E> graph, HashMap<Triple<V, V, V>, Integer> not_in_hole,
			Integer[] in_path, ArrayList<ArrayList<V>> adjList, V a, V b, V c) {
		ArrayList<V> vertices = new ArrayList<>(graph.vertexSet());
		int indexC = vertices.indexOf(c);
		in_path[indexC] = 1;
		for (int i = 0; i < vertices.size(); i++) {
			V d = vertices.get(i);
			if (!d.equals(a) && !d.equals(b)) {
				if (adjList.get(indexC).contains(d)) {
					if (!adjList.get(i).contains(a) || !adjList.get(i).contains(b)) {
//						System.out.println("P4 in G");
					}
					Triple<V, V, V> triple = new Triple<V, V, V>(b, c, d);
					if (!not_in_hole.containsKey(triple)) {
						not_in_hole.put(triple, 0);
					}
					if (in_path[i] == 1) {
						return true;
					} else if (not_in_hole.get(triple) == 0) {
						boolean hasHole = process(graph, not_in_hole, in_path, adjList, b, c, d);
						if (hasHole)
							return true;
					}
				}
			}
		}
		in_path[indexC] = 0;
		Triple<V, V, V> triple = new Triple<V, V, V>(a, b, c);
		not_in_hole.put(triple, 1);
		triple = new Triple<V, V, V>(c, b, a);
		not_in_hole.put(triple, 1);
		return false;
	}
	
	// weak decomposition algorithmen
	public static <V, E> Triple<V, V, V> weakDecomposition(Graph<V, E> graph) {
		List<V> A = new ArrayList<>();
		List<V> vertices = new ArrayList<>(graph.vertexSet());
		for (int i = 0; i < vertices.size(); i++) {
			if (graph.degreeOf(vertices.get(i)) < vertices.size()) {
				A.add(vertices.get(i));
				break;
			}
		}
		List<V> N = Graphs.neighborListOf(graph, A.get(0));
		List<V> R = new ArrayList<>(vertices);
		R.removeAll(new HashSet<V>(N));
		R.removeAll(new HashSet<V>(A));
		for (int i = 0; i < N.size(); i++) {
			V n = N.get(i);
			List<V> großeSchnittmenge = new ArrayList<>();
			for (int j = 0; j < R.size(); j++) {
				V r = R.get(j);
				if (!graph.containsEdge(r, n)) {
					N.remove(n);
					List<V> schnittMenge = new ArrayList<>();
					for (V v : Graphs.neighborListOf(graph, n)) {
						if (R.contains(v) && !N.contains(v)) {
							schnittMenge.add(v);
						}
					}
					N.addAll(schnittMenge);
					A.add(n);
					großeSchnittmenge.addAll(schnittMenge);
				}
			}
			R.removeAll(großeSchnittmenge);

		}
		return new Triple<V, V, V>(A, N, R);
	}

	public static <V, E> ListTriple<V, V, V> weakDecomposition(Graph<V, E> graph) {
		List<V> A = new ArrayList<>();
		List<V> vertices = new ArrayList<>(graph.vertexSet());
		for (int i = 0; i < vertices.size(); i++) {
			if (graph.degreeOf(vertices.get(i)) < vertices.size()) {
				A.add(vertices.get(i));
				break;
			}
		}
		List<V> N = Graphs.neighborListOf(graph, A.get(0));
		List<V> R = new ArrayList<>(vertices);
		R.removeAll(new HashSet<V>(N));
		R.removeAll(new HashSet<V>(A));
		for (int i = 0; i < N.size(); i++) {
			V n = N.get(i);
			List<V> großeSchnittmenge = new ArrayList<>();
			for (int j = 0; j < R.size(); j++) {
				V r = R.get(j);
				if (!graph.containsEdge(r, n)) {
					N.remove(n);
					List<V> schnittMenge = new ArrayList<>();
					for (V v : Graphs.neighborListOf(graph, n)) {
						if (R.contains(v) && !N.contains(v)) {
							schnittMenge.add(v);
						}
					}
					N.addAll(schnittMenge);
					A.add(n);
					großeSchnittmenge.addAll(schnittMenge);
				}
			}
			R.removeAll(großeSchnittmenge);

		}
		return new ListTriple<V, V, V>(A, N, R);
	}
	
	// gets a permutation from a graph and a list of vertices
	private static <V, E> List<List<V>> getPermutation(Graph<V, E> graph, List<V> vertices) {
		LinkedList<List<V>> permutationList = new LinkedList<>();
		if (vertices.isEmpty()) {
			return new LinkedList<>();
		} else if (vertices.size() == 1) {
			LinkedList<V> node1List = new LinkedList<>();
			node1List.add(vertices.get(0));
			permutationList.add(node1List);
			return permutationList;
		}
		List<V> nodesRight = vertices;
		V node1 = nodesRight.get(0);
		Set<E> edges = graph.edgesOf(node1);
		List<V> nodesLeft = new ArrayList<>();
		for (E e : edges) {
			V tmpNode = graph.getEdgeSource(e);
			if (node1.equals(tmpNode)) {
				tmpNode = graph.getEdgeTarget(e);
			}
			if (vertices.contains(tmpNode)) {
				nodesLeft.add(tmpNode);
			}
		}
		nodesRight.removeAll(nodesLeft);
		nodesRight.remove(node1);
		List<List<V>> leftSide = getPermutation(graph, nodesLeft);
		List<List<V>> rightSide = getPermutation(graph, nodesRight);
		if (!leftSide.isEmpty()) {
			for (List<V> leftElement : leftSide) {
				permutationList.add(leftElement);
			}
		}
		LinkedList<V> node1List = new LinkedList<>();
		node1List.add(node1);
		permutationList.add(node1List);
		if (!rightSide.isEmpty()) {
			for (List<V> rightElement : rightSide) {
				permutationList.add(rightElement);
			}
		}
		return permutationList;
	}
	
	// returns a special vertex. Used for quasi treshhold
	private static <V> V getSpecialVertex(ArrayList<V> allV, HashMap<V, Triple<Integer, Integer, Integer>> degreeMap,
			List<V> neighborListOf, V vj) {
		int vjDegree = degreeMap.get(vj).getFirst();
		Pair<Integer, V> largestIndegree = new Pair<Integer, V>(-1, null);
		for (int i = 0; i < neighborListOf.size(); i++) {
			V vi = neighborListOf.get(i);
			if (degreeMap.get(vi).getSecond() > largestIndegree.getFirst())
				largestIndegree = new Pair<Integer, V>(degreeMap.get(vi).getSecond(), vi);
		}
		if (largestIndegree.getSecond() == null) {
			return null;
		}
		V vi = largestIndegree.getSecond();
		int viDegree = degreeMap.get(vi).getFirst();
		if (vjDegree < viDegree || (viDegree == vjDegree && allV.indexOf(vi) < allV.indexOf(vj))) {
			return vi;
		}
		return null;
	}
}

class ListTriple<A, B, C> {
	List<A> first;
	List<B> secound;
	List<C> third;

	public ListTriple(List<A> firstElement, List<B> secoundElement, List<C> thirdElement) {
		this.first = firstElement;
		this.secound = secoundElement;
		this.third = thirdElement;
	}
}