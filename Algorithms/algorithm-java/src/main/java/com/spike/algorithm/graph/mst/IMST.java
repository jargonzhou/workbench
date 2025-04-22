package com.spike.algorithm.graph.mst;


import com.spike.algorithm.graph.core.Edge;

/**
 * 最小生成树(Minimum Spanning Trees, MST)接口.
 */
public interface IMST {

    /**
     * 最小生成树中所有边.
     */
    Iterable<Edge> edges();

    /**
     * 最小生成树的权重.
     */
    default double weight() {
        double result = 0;
        for (Edge e : this.edges()) {
            result += e.weight();
        }
        return result;
    }
}
