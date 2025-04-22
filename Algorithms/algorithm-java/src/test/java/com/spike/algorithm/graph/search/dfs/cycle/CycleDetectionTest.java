package com.spike.algorithm.graph.search.dfs.cycle;

import com.spike.algorithm.graph.core.Graph;
import org.junit.jupiter.api.Test;

public class CycleDetectionTest {
    @Test
    public void cycle() {
        int[] vs = new int[]{0, 1, 2, 3, 4, 5};
        Graph G = new Graph(vs.length);

        G.addEdge(0, 5);
        G.addEdge(3, 5);
        G.addEdge(5, 4);
        G.addEdge(4, 3);

        CycleDetection cd = new CycleDetection(G);
        if (cd.hasCycle()) {
            for (int v : cd.cycle()) {
                System.out.print(v + " "); // 3 5 4 3
            }
            System.out.println();
        }

    }
}
