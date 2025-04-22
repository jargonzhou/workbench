package com.spike.algorithm.graph.sp;

import com.spike.algorithm.graph.EdgeWeightedDigraphTest;
import com.spike.algorithm.graph.core.DirectedEdge;
import com.spike.algorithm.graph.core.EdgeWeightedDigraph;
import com.spike.algorithm.support.trace.Trace;
import com.spike.algorithm.support.trace.TraceAction;
import org.junit.jupiter.api.Test;

public class ISPTest {
    @Test
    public void dijkstra() {
        EdgeWeightedDigraph G = new EdgeWeightedDigraphTest().doCreate();
        System.out.println(G.dump(false));
        System.out.println(TraceAction.ns.dump());

        int s = 0;
        DijkstraSP sp = new DijkstraSP(G, s);

        Trace trace = sp.trace();
        System.out.println(trace.dumpTrace());

        System.out.println();
        for (int v = 0; v < G.V(); v++) {
            System.out.print(s + " to " + v);
            System.out.printf(" (%4.2f): ", sp.distTo(v));
            if (sp.hasPathTo(v)) {
                for (DirectedEdge e : sp.pathTo(v)) {
                    System.out.print(e.from() + "->" + e.to() + "(" + e.weight() + ") ");
                }
            }
            System.out.println();
        }
    }
}
