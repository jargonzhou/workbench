package com.spike.algorithm.graph.search.dfs.cc;


import com.spike.algorithm.adt.Bag;
import com.spike.algorithm.graph.core.Edge;
import com.spike.algorithm.graph.core.Graph;
import com.spike.algorithm.support.trace.Trace;
import com.spike.algorithm.support.trace.Traceable;
import com.spike.algorithm.graph.search.IDFS;

/**
 * 使用深度优先搜索找出图中的所有连通分量.
 */
public class ConnectedComponents implements IDFS<Graph>, Traceable {
    private final Graph G;
    private boolean[] marked; // 顶点是否访问过, 索引: 顶点
    private int[] id; // 索引: 顶点, 值: 连通分量的标识
    private int count; // 图中连通分量的数量

    private final Trace trace = new Trace();

    public ConnectedComponents(Graph G) {
        this.G = G;
        this.marked = new boolean[G.V()];
        this.id = new int[G.V()];
        this.count = 0;

        for (int s = 0; s < G.V(); s++) {
            // 遍历所有顶点, 使用DFS找出各顶点所在的连通分量
            if (!marked[s]) {
                this.dfs(G, s);
                count++;// 生成了新的连通分量
            }
        }
    }

    @Override
    public void dfs(Graph G, int v) {
        marked[v] = true;
        id[v] = count; // 指定顶点的连通分量编号

        for (int w : G.adj(v)) {
            if (!marked[w]) {
                trace.add(new Edge(v, w));
                this.dfs(G, w);
            }
        }
    }

    /**
     * 顶点v和w是否连通.
     */
    public boolean connected(int v, int w) {
        return id[v] == id[w];
    }

    /**
     * 图中连通分量的数量.
     */
    public int count() {
        return count;
    }

    /**
     * 顶点v所在的连通分量编号(0 ~ count()-1).
     */
    public int id(int v) {
        return id[v];
    }

    public void dump() {
        @SuppressWarnings("unchecked")
        Bag<Integer>[] ccs = (Bag<Integer>[]) new Bag[count];
        for (int cc = 0; cc < count; cc++) {
            ccs[cc] = new Bag<>();
        }
        for (int v = 0; v < G.V(); v++) {
            ccs[this.id(v)].add(v);
        }
        for (int cc = 0; cc < count; cc++) {
            System.out.println("CC[" + cc + "]: " + ccs[cc]);
        }
    }

    @Override
    public Trace trace() {
        return trace;
    }
}
