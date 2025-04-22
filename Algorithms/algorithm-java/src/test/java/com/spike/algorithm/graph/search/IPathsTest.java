package com.spike.algorithm.graph.search;

import com.spike.algorithm.graph.core.Graph;
import org.junit.jupiter.api.Test;

import java.util.Iterator;
import java.util.Objects;

public class IPathsTest {
    @Test
    public void dfs() {
        Graph G = new IGraphSearchTest().create();
        IPaths<Graph> paths = new DepthFirstPaths<>(G, 0);

        Iterable<Integer> pathTo = paths.pathTo(5);
        if (Objects.nonNull(pathTo)) {
            Iterator<Integer> it = pathTo.iterator();
            while (it.hasNext()) {
                System.out.print(it.next() + " ");
            }
            System.out.println();
        } else {
            System.out.println("No path");
        }
    }
}
