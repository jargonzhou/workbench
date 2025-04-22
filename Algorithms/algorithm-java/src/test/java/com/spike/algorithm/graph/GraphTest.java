package com.spike.algorithm.graph;

import com.spike.algorithm.graph.core.Graph;
import org.junit.jupiter.api.Test;

public class GraphTest {

    @Test
    public void create() {
        Graph G = doCreate();

        System.out.println(G.dump(true));
    }

    public Graph doCreate() {
        // tinyG.txt: 13 vertex, 13 edges
        int[] vs = new int[]{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};
        Graph G = new Graph(vs.length);

        G.addEdge(0, 5);
        G.addEdge(4, 3);
        G.addEdge(0, 1);
        G.addEdge(9, 12);
        G.addEdge(6, 4);
        G.addEdge(5, 4);
        G.addEdge(0, 2);
        G.addEdge(11, 12);
        G.addEdge(9, 10);
        G.addEdge(0, 6);
        G.addEdge(7, 8);
        G.addEdge(9, 11);
        G.addEdge(5, 3);
        return G;
    }
}
