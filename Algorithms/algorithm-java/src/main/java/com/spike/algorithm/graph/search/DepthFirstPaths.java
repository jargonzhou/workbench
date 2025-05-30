package com.spike.algorithm.graph.search;


import com.spike.algorithm.adt.Stack;
import com.spike.algorithm.graph.core.Edge;
import com.spike.algorithm.graph.core.IGraph;
import com.spike.algorithm.support.trace.Trace;
import com.spike.algorithm.support.trace.Traceable;

/**
 * 使用深度优先搜索查找图中路径. 适用于无向图和有向图.
 * <p>
 * 使用了路径中父顶点链<code>edgeTo</code>.
 */
public class DepthFirstPaths<GRAPH extends IGraph> implements IPaths<GRAPH>, IDFS<GRAPH>, Traceable {

    private final GRAPH G;
    private final int s; // 开始顶点

    private boolean[] marked; // 顶点是否访问过, 索引: 顶点
    private int[] edgeTo; // 从开始顶点s到一个顶点的路径上的最后一个顶点(父顶点), 索引: 顶点, 值: 父顶点

    private final Trace trace = new Trace();

    public DepthFirstPaths(GRAPH G, int s) {
        this.G = G;
        this.s = s;
        this.marked = new boolean[G.V()];
        this.edgeTo = new int[G.V()];

        this.dfs(G, s);
    }

    @Override
    public void dfs(GRAPH G, int v) {
        marked[v] = true;

        for (int w : G.adj(v)) {
            if (!marked[w]) {// 将v置为w的父顶点, 在w上执行递归调用
                trace.add(new Edge(v, w));
                edgeTo[w] = v;
                this.dfs(G, w);
            }
        }
    }

    @Override
    public GRAPH G() {
        return G;
    }

    @Override
    public int s() {
        return s;
    }

    @Override
    public boolean hasPathTo(int v) {
        return marked[v];
    }

    @Override
    public Iterable<Integer> pathTo(int v) {
        if (!this.hasPathTo(v)) {
            return null;
        }

        // 父顶点链入栈
        Stack<Integer> stack = new Stack<>();
        for (int w = v; w != s; w = edgeTo[w]) {
            stack.push(w);
        }
        stack.push(s);
        return stack;
    }

    @Override
    public Trace trace() {
        return trace;
    }
}
