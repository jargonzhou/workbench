package com.spike.algorithm.graph.search;

import com.spike.algorithm.graph.core.Graph;

/**
 * 图中单点搜索.
 */
public interface IGraphSearch {
    /**
     * 无向图G.
     */
    Graph G();

    /**
     * 起点.
     */
    int s();

    /**
     * 顶点v是否与起点s连通.
     */
    boolean marked(int v);

    /**
     * 与起点s连通的顶点总数.
     */
    int count();
}
