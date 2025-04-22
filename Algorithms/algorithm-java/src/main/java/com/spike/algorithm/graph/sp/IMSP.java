package com.spike.algorithm.graph.sp;

import com.spike.algorithm.graph.core.DirectedEdge;
import com.spike.algorithm.graph.core.EdgeWeightedDigraph;

import java.util.List;

/**
 * 有向图中的最短路径.
 */
public interface IMSP {

    EdgeWeightedDigraph G();

    /**
     * 起点
     */
    List<Integer> ss();

    /**
     * 从起点到v的距离. 不存在路径为无穷大.
     */
    double distTo(int s, int v);

    /**
     * 是否存在从起点到v的路径.
     */
    boolean hasPathTo(int s, int v);

    /**
     * 从起点到v的路径. 不存在为null.
     */
    Iterable<DirectedEdge> pathTo(int s, int v);
}
