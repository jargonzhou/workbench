package com.spike.algorithm.graph.sp;

import com.spike.algorithm.graph.core.DirectedEdge;
import com.spike.algorithm.graph.core.EdgeWeightedDigraph;

/**
 * 有向图中的单点最短路径.
 */
public interface ISP {
    EdgeWeightedDigraph G();

    /**
     * 起点
     */
    int s();

    /**
     * 从起点到v的距离. 不存在路径为无穷大.
     */
    double distTo(int v);

    /**
     * 是否存在从起点到v的路径.
     */
    boolean hasPathTo(int v);

    /**
     * 从起点到v的路径. 不存在为null.
     */
    Iterable<DirectedEdge> pathTo(int v);
}
