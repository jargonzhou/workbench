package com.spike.algorithm.graph.search.dfs.cycle;

import com.spike.algorithm.graph.core.Digraph;
import org.junit.jupiter.api.Test;

public class DirectedCycleDetectionTest {
    @Test
    public void cycle() {
        int[] vs = new int[]{0, 1, 2, 3, 4, 5};
        Digraph DG = new Digraph(vs.length);

        DG.addEdge(0, 5);
        DG.addEdge(3, 5);
        DG.addEdge(5, 4);
        DG.addEdge(4, 3);

        DirectedCycleDetection dcd = new DirectedCycleDetection(DG);
        if (dcd.hasCycle()) {
            for (int v : dcd.cycle()) {
                System.out.print(v + " ");
            }
            System.out.println();
        }

    }
}
