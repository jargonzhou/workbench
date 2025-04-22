package com.spike.algorithm.graph;

import com.spike.algorithm.graph.core.Digraph;
import org.junit.jupiter.api.Test;

public class DigraphTest {
    @Test
    public void create() {
        Digraph G = doCreate();

        System.out.println(G.dump(false));
    }

    public Digraph doCreate() {
        // tinyDG.txt: 13 vertex, 22 edges
        int[] vs = new int[]{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};
        Digraph DG = new Digraph(vs.length);

        DG.addEdge(0, 5);
        DG.addEdge(4, 2);
        DG.addEdge(2, 3);
        DG.addEdge(3, 2);
        DG.addEdge(6, 0);
        DG.addEdge(0, 1);
        DG.addEdge(2, 0);
        DG.addEdge(11, 12);
        DG.addEdge(12, 9);
        DG.addEdge(9, 10);
        DG.addEdge(9, 11);
        DG.addEdge(7, 9);
        DG.addEdge(10, 12);
        DG.addEdge(11, 4);
        DG.addEdge(4, 3);
        DG.addEdge(3, 5);
        DG.addEdge(6, 8);
        DG.addEdge(8, 6);
        DG.addEdge(5, 4);
        DG.addEdge(0, 5);
        DG.addEdge(6, 4);
        DG.addEdge(6, 9);
        DG.addEdge(7, 6);

        return DG;
    }
}
