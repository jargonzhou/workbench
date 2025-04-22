package com.spike.algorithm.graph.mst;

import com.spike.algorithm.adt.Queue;
import com.spike.algorithm.graph.core.Edge;
import com.spike.algorithm.graph.core.EdgeWeightedGraph;
import com.spike.algorithm.support.trace.Trace;
import com.spike.algorithm.support.trace.Traceable;
import com.spike.algorithm.sorting.MinPQ;

public class LazyPrimMST implements IMST, Traceable {
    private boolean[] marked; // MST的顶点
    private Queue<Edge> mst; // MST的边
    private MinPQ<Edge> pq; // 横切边: 包含失效的边
    // 失效的边: 连接新加入MST中的顶点与其他已经在树中的顶点的所有边已失效

    private final Trace trace = new Trace();

    public LazyPrimMST(EdgeWeightedGraph G, int s) {
        pq = new MinPQ<>();
        marked = new boolean[G.V()];
        mst = new Queue<>();

        this.visit(G, s); // 假设: 图是连通的

        while (!pq.isEmpty()) {
            Edge e = pq.delMin(); // 权重最小的边

            int v = e.either();
            int w = e.other(v);

            if (marked[v] && marked[w]) { // 跳过失效的边
                continue;
            }

            mst.enqueue(e); // 将边添加到树中
            trace.add(e);
            // 将顶点添加到树中
            if (!marked[v]) {
                this.visit(G, v);
            }
            if (!marked[w]) {
                this.visit(G, w);
            }
        }
    }

    private void visit(EdgeWeightedGraph G, int v) {
        marked[v] = true; // 标记v

        for (Edge e : G.adj(v)) {
            // 将所有连接v但未被标记的顶点的边加入pq
            if (!marked[e.other(v)]) {
                pq.insert(e);
            }
        }
    }


    @Override
    public Iterable<Edge> edges() {
        return mst;
    }

    @Override
    public Trace trace() {
        return trace;
    }
}
