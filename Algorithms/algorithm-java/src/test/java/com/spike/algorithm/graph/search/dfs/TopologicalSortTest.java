package com.spike.algorithm.graph.search.dfs;

import com.spike.algorithm.graph.core.Digraph;
import com.spike.algorithm.graph.search.dfs.TopologicalSort;
import org.junit.jupiter.api.Test;

public class TopologicalSortTest {
    @Test
    public void sort() {
        int[] vs = new int[]{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};
        Digraph DG = new Digraph(vs.length);

        DG.addEdge(0, 1);
        DG.addEdge(0, 5);
        DG.addEdge(0, 6);
        DG.addEdge(2, 0);
        DG.addEdge(2, 3);
        DG.addEdge(3, 5);
        DG.addEdge(5, 4);
        DG.addEdge(6, 4);
        DG.addEdge(6, 9);
        DG.addEdge(7, 6);
        DG.addEdge(8, 7);
        DG.addEdge(9, 10);
        DG.addEdge(9, 11);
        DG.addEdge(9, 12);
        DG.addEdge(11, 12);

        TopologicalSort ts = new TopologicalSort(DG);
        if (ts.isDAG()) {
            for (int v : ts.order()) {
                System.out.print(v + " ");
            }
            System.out.println();
        }
    }
}
