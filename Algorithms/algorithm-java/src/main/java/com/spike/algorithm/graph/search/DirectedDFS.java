package com.spike.algorithm.graph.search;


import com.spike.algorithm.graph.core.Digraph;
import com.spike.algorithm.graph.core.Edge;
import com.spike.algorithm.support.trace.Trace;
import com.spike.algorithm.support.trace.Traceable;

/**
 * 有向图中的深度优先搜索, 确定可达性.
 */
public class DirectedDFS implements IDFS<Digraph>, Traceable {

    private boolean[] marked; // 顶点是否访问过, 索引: 顶点

    private final Trace trace = new Trace();

    // s: // 开始顶点
    public DirectedDFS(Digraph DG, int s) {
        this.marked = new boolean[DG.V()];

        this.dfs(DG, s);
    }

    public DirectedDFS(Digraph DG, Iterable<Integer> sources) {
        this.marked = new boolean[DG.V()];
        for (int s : sources) {
            this.dfs(DG, s);
        }
    }

    @Override
    public void dfs(Digraph DG, int v) {
        marked[v] = true;

        for (int w : DG.adj(v)) {
            if (!marked[w]) {
                trace.add(new Edge(v, w));
                this.dfs(DG, w);
            }
        }
    }

    public boolean marked(int v) {
        return marked[v];
    }

    @Override
    public Trace trace() {
        return trace;
    }
}
