package com.spike.algorithm.graph.search.dfs;


import com.spike.algorithm.graph.core.Digraph;
import com.spike.algorithm.graph.search.DirectedDFS;

/**
 * 有向图中的传递闭包.
 */
public class TransitiveClosure {

    private DirectedDFS[] all; // 在所有顶点上执行DFS, 索引: 顶点

    public TransitiveClosure(Digraph DG) {
        all = new DirectedDFS[DG.V()];
        for (int v = 0; v < DG.V(); v++) {
            all[v] = new DirectedDFS(DG, v);
        }
    }

    /**
     * 顶点v可否可达顶点w.
     */
    public boolean reachable(int v, int w) {
        return all[v].marked(w);
    }
}
