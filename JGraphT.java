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
}
