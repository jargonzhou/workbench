package com.spike.algorithm.graph.mst;

import com.spike.algorithm.graph.core.Edge;
import com.spike.algorithm.graph.core.EdgeWeightedGraph;
import com.spike.algorithm.support.trace.Trace;
import org.junit.jupiter.api.Test;

public class IMSTTest {
    @Test
    public void lazyPrim() {
        EdgeWeightedGraph EWG = this.create();
        System.out.println(EWG.dump(false));
        System.out.println("ns");

        int s = 0;
        LazyPrimMST mst = new LazyPrimMST(EWG, s);

        Trace trace = mst.trace();
        System.out.println(trace.dumpWithoutSource());
        System.out.println();

        System.out.println("Weight: " + mst.weight()); // Weight: 1.81
    }

    @Test
    public void kruskal() {
        EdgeWeightedGraph EWG = this.create();
        System.out.println(EWG.dump(false));
        System.out.println("ns");

        KruskalMST mst = new KruskalMST(EWG);

        Trace trace = mst.trace();
        System.out.println(trace.dumpWithoutSource());
        System.out.println();

        System.out.println("Weight: " + mst.weight()); // Weight: 1.81
    }

    public EdgeWeightedGraph create() {
        // tinyEWG: 8 vertex, 16 edge
        EdgeWeightedGraph EWG = new EdgeWeightedGraph(8);
        EWG.addEdge(new Edge(4, 5, 0.35));
        EWG.addEdge(new Edge(4, 7, 0.37));
        EWG.addEdge(new Edge(5, 7, 0.28));
        EWG.addEdge(new Edge(0, 7, 0.16));
        EWG.addEdge(new Edge(1, 5, 0.32));
        EWG.addEdge(new Edge(0, 4, 0.38));
        EWG.addEdge(new Edge(2, 3, 0.17));
        EWG.addEdge(new Edge(1, 7, 0.19));
        EWG.addEdge(new Edge(0, 2, 0.26));
        EWG.addEdge(new Edge(1, 2, 0.36));
        EWG.addEdge(new Edge(1, 3, 0.29));
        EWG.addEdge(new Edge(2, 7, 0.34));
        EWG.addEdge(new Edge(6, 2, 0.40));
        EWG.addEdge(new Edge(3, 6, 0.52));
        EWG.addEdge(new Edge(6, 0, 0.58));
        EWG.addEdge(new Edge(6, 4, 0.93));
        return EWG;
    }
}
