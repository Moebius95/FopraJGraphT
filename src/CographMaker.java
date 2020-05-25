import org.jgrapht.*;
import org.jgrapht.graph.*;
import org.jgrapht.nio.*;
import org.jgrapht.nio.dot.DOTExporter;
import org.jgrapht.traverse.*;
import org.jprapht.graph;

import java.io.*;
import java.net.*;
import java.util.*;

public final class CographMaker
{
    private CographMaker()
    {
    }

    public static void main(String[] args)
            throws URISyntaxException,
            ExportException, IOException
            {

    	  File dir = new File("Export");
    	  File[] directoryListing = dir.listFiles();
    	  if (directoryListing != null) {
    	    for (File el : directoryListing) {
    	    	Graph<Integer, DefaultEdge> test = txtToGraph("Export/" + el.getName());
    	    	System.out.println(el.getName() + " ist ein Thresholdgraph: " + isThresholdgraph(test));
    	    }
    	  }
    }
    
    //returns true iff graph g is a Cograph
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