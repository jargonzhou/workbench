package com.spike.algorithm.graph.search.dfs.cycle;


import com.spike.algorithm.adt.Stack;
import com.spike.algorithm.graph.core.Digraph;
import com.spike.algorithm.graph.search.IDFS;

/**
 * 有向环检测, 使用深度优先搜索.
 */
public class DirectedCycleDetection implements IDFS<Digraph> {

    private boolean[] marked; // 顶点是否访问过, 索引: 顶点
    private int[] edgeTo; // 从开始顶点s到一个顶点的路径上的最后一个顶点(父顶点), 索引: 顶点, 值: 父顶点

    private Stack<Integer> cycle; // 如果存在环, 环上的顶点

    private boolean[] onStack; // 递归调用栈上的顶点, 索引: 顶点

    public DirectedCycleDetection(Digraph DG) {
        this.marked = new boolean[DG.V()];
        this.onStack = new boolean[DG.V()];
        this.edgeTo = new int[DG.V()];

        for (int v = 0; v < DG.V(); v++) {// 在每个顶点上调用DFS
            if (!marked[v]) {
                this.dfs(DG, v);
            }
        }
    }

    @Override
    public void dfs(Digraph DG, int v) {
        onStack[v] = true; // 入栈

        marked[v] = true;
        for (int w : DG.adj(v)) {
            if (this.hasCycle()) {
                return;
            } else if (!marked[w]) { // w未访问过
                edgeTo[w] = v;
                this.dfs(DG, w);
            } else if (onStack[w]) { // w已访问过, 且在栈中
                cycle = new Stack<>();
                for (int x = v; x != w; x = edgeTo[x]) {
                    cycle.push(x);
                }
                cycle.push(w);
                cycle.push(v);
            }
        }

        onStack[v] = false; // 出栈
    }

    /**
     * 图中是否有环.
     */
    public boolean hasCycle() {
        return cycle != null;
    }

    /**
     * 返回一个由顶点构成的环.
     */
    public Iterable<Integer> cycle() {
        return cycle;
    }
}
