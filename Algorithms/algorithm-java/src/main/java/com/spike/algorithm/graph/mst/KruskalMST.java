package com.spike.algorithm.graph.mst;

import com.spike.algorithm.adt.Queue;
import com.spike.algorithm.example.uf.UF;
import com.spike.algorithm.graph.core.Edge;
import com.spike.algorithm.graph.core.EdgeWeightedGraph;
import com.spike.algorithm.support.trace.Trace;
import com.spike.algorithm.support.trace.Traceable;
import com.spike.algorithm.sorting.MinPQ;

public class KruskalMST implements IMST, Traceable {
    private Queue<Edge> mst;

    private final Trace trace = new Trace();

    public KruskalMST(EdgeWeightedGraph G) {
        mst = new Queue<>();
        MinPQ<Edge> pq = new MinPQ<>(); // 优先级队列
        for (Edge e : G.edges()) {
            pq.insert(e);
        }
        UF uf = new UF(G.V());

        while (!pq.isEmpty() && mst.size() < G.V() - 1) {
            Edge e = pq.delMin(); // 权重最小的边
            int v = e.either();
            int w = e.other(v);

            if (uf.connected(v, w)) { // 忽略失效的边
                continue;
            }

            uf.union(v, w); // 合并分量

            mst.enqueue(e); // 将边添加到MST中
            trace.add(e);
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
