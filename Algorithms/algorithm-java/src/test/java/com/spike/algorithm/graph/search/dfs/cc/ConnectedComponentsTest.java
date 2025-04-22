package com.spike.algorithm.graph.search.dfs.cc;

import com.spike.algorithm.graph.GraphTest;
import com.spike.algorithm.graph.core.Graph;
import com.spike.algorithm.support.trace.Trace;
import org.junit.jupiter.api.Test;

public class ConnectedComponentsTest {
    @Test
    public void cc() {
        Graph G = new GraphTest().doCreate();

        ConnectedComponents cc = new ConnectedComponents(G);
        cc.dump();
        System.out.println();

        System.out.print(G.dump(false));
        System.out.print("ns");
        Trace trace = cc.trace();
        System.out.print(trace.dump());
    }
}
