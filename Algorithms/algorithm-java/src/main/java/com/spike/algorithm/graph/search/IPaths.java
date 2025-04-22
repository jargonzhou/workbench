package com.spike.algorithm.graph.search;

import com.spike.algorithm.graph.core.IGraph;

/**
 * 图中单点路径.
 */
public interface IPaths<GRAPH extends IGraph> {
    /**
     * 无向图或无向图G.
     */
    GRAPH G();

    /**
     * 起点.
     */
    int s();

    /**
     * 是否存在从起点s到顶点v的路径.
     */
    boolean hasPathTo(int v);

    /**
     * 开始顶点s到顶点v的路径, 不存在返回null.
     */
    Iterable<Integer> pathTo(int v);
}
