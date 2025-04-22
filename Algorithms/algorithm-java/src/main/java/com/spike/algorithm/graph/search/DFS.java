package com.spike.algorithm.graph.search;

import com.spike.algorithm.graph.core.Edge;
import com.spike.algorithm.graph.core.Graph;
import com.spike.algorithm.support.trace.Trace;
import com.spike.algorithm.support.trace.Traceable;

/**
 * 深度优先搜索(Depth First Search, DFS).
 *
 * <p>访问顶点, 将其标记为已访问, 再递归的访问其所有未访问过的邻接点.
 */
public class DFS implements IGraphSearch, IDFS<Graph>, Traceable {

    private final Graph G;
    private final int s; // 起点

    private boolean[] marked; // 顶点是否访问过, 索引: 顶点
    private int count; // 已访问过的顶点数量

    private Trace trace = new Trace();

    public DFS(Graph G, int s) {
        this.G = G;
        this.s = s;
        this.count = 0;
        this.marked = new boolean[G.V()];

        // 从起点开始访问
        this.dfs(G, s);
    }

    @Override
    public void dfs(Graph G, int v) {
        marked[v] = true;
        count++;

        for (int w : G.adj(v)) {
            if (!marked(w)) {// 邻接顶点中未访问过的顶点, 执行递归调用
                trace.add(new Edge(v, w));
                this.dfs(G, w);
            }
        }
    }

    @Override
    public Graph G() {
        return this.G;
    }

    @Override
    public int s() {
        return this.s;
    }

    @Override
    public boolean marked(int v) {
        return marked[v];
    }

    @Override
    public int count() {
        return count;
    }

    @Override
    public Trace trace() {
        return trace;
    }
}
