package com.spike.algorithm.graph.search.dfs.cycle;


import com.spike.algorithm.adt.Stack;
import com.spike.algorithm.graph.core.Graph;
import com.spike.algorithm.graph.search.IDFS;

/**
 * 无向图中环检测: 使用深度优先搜索.
 *
 * <p>假设不存在自环或平行边.
 */
public class CycleDetection implements IDFS.IDFSWithFather<Graph> {
    private boolean[] marked; // 顶点是否访问过, 索引: 顶点
    private boolean hasCycle = false; // 是否有环标志
    private int[] edgeTo; // 从开始顶点s到一个顶点的路径上的最后一个顶点(父顶点), 索引: 顶点, 值: 父顶点
    private Stack<Integer> cycle;

    public CycleDetection(Graph G) {
        this.marked = new boolean[G.V()];
        this.edgeTo = new int[G.V()];

        for (int s = 0; s < G.V(); s++) {
            if (!marked[s]) {
                this.dfs(G, s, s);
            }
        }
    }

    // 通过顶点u访问其邻接顶点v的深度优先搜索: u->v
    @Override
    public void dfs(Graph G, int v, int u) {

        marked[v] = true;

        for (int w : G.adj(v)) {
            if (hasCycle) {
                return;
            }

            if (!marked[w]) {
                edgeTo[w] = v;
                this.dfs(G, w, v);
            } else if (w != u) { // w已访问过, 构成环(u->v->w->u)
                hasCycle = true;
                cycle = new Stack<>(); // 构造环
                for (int x = v; x != w; x = edgeTo[x]) { // v ~> x -> w
                    cycle.push(x);
                }
                cycle.push(w); // w -> v
                cycle.push(v);
            }
        }
    }

    public boolean hasCycle() {
        return hasCycle;
    }

    /**
     * 返回一个由顶点构成的环.
     */
    public Iterable<Integer> cycle() {
        return cycle;
    }
}
