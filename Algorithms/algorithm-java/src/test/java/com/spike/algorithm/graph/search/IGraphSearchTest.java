package com.spike.algorithm.graph.search;

import com.spike.algorithm.graph.DigraphTest;
import com.spike.algorithm.graph.core.Digraph;
import com.spike.algorithm.graph.core.Graph;
import com.spike.algorithm.support.trace.Trace;
import org.junit.jupiter.api.Test;

public class IGraphSearchTest {
    @Test
    public void dfs() {
        Graph G = this.create();
        System.out.println(G.dump(false));
        System.out.println("ns");

        DFS search = new DFS(G, 0);
        System.out.println("hn 0");
        System.out.println("ln 0 \"0(v)\"");
        System.out.println("ns");

        Trace trace = search.trace();
        System.out.println(trace.dump());
    }

    @Test
    public void ddfs() {
        Digraph DG = new DigraphTest().doCreate();
        System.out.print(DG.dump(false));
        System.out.println("ns");

        DirectedDFS ddfs = new DirectedDFS(DG, 2);
        System.out.println("hn 2");
        System.out.println("ln 2 \"2(v)\"");
        System.out.println("ns");

        Trace trace = ddfs.trace();
        System.out.print(trace.dump());
    }

    @Test
    public void bfs() {
        Graph G = this.create();
        System.out.println(G.dump(false));
        System.out.println("ns");

        BFS<Graph> search = new BFS<>(G, 0);
        System.out.println("hn 0");
        System.out.println("ln 0 \"0(v)\"");
        System.out.println("ns");

        Trace trace = search.trace();
        System.out.println(trace.dump());

        // more: 顶点间距离度量(最短路径).
    }

    public Graph create() {
        // tinyCG.txt: 6 vertex, 8 edge
        int[] vs = new int[]{0, 1, 2, 3, 4, 5};
        Graph G = new Graph(vs.length);

        G.addEdge(0, 5);
        G.addEdge(2, 4);
        G.addEdge(2, 3);
        G.addEdge(1, 2);
        G.addEdge(0, 1);
        G.addEdge(3, 4);
        G.addEdge(3, 5);
        G.addEdge(0, 2);
        return G;
    }
}
