package com.spike.algorithm.graph.search;

import com.spike.algorithm.graph.core.IGraph;

/**
 * 广度优先搜索接口.
 */
public interface IBFS<GRAPH extends IGraph> {
    void bfs(GRAPH G, int s);
}
