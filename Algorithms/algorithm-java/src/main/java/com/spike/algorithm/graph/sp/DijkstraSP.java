package com.spike.algorithm.graph.sp;

import com.spike.algorithm.adt.Stack;
import com.spike.algorithm.graph.core.DirectedEdge;
import com.spike.algorithm.graph.core.EdgeWeightedDigraph;
import com.spike.algorithm.sorting.IndexMinPQ;
import com.spike.algorithm.support.trace.Trace;
import com.spike.algorithm.support.trace.TraceLink;
import com.spike.algorithm.support.trace.Traceable;

public class DijkstraSP implements ISP, Traceable {
    private final EdgeWeightedDigraph G;
    private final int s; // 起点

    private DirectedEdge[] edgeTo;
    private double[] distTo;

    private IndexMinPQ<Double> pq; // 优先队列

    private final Trace trace = new Trace();

    public DijkstraSP(EdgeWeightedDigraph G, int s) {
        this.G = G;
        this.s = s;

        this.edgeTo = new DirectedEdge[G.V()];
        this.distTo = new double[G.V()];
        this.pq = new IndexMinPQ<>(G.V());

        for (int v = 0; v < G.V(); v++) {
            distTo[v] = Double.POSITIVE_INFINITY;
        }
        distTo[s] = 0;
        pq.insert(s, 0.0);
        while (!pq.isEmpty()) {
            this.relax(G, pq.delMin()); // 选择离起点最近的非树顶点
        }
    }

    // 边松弛
    private void relax(DirectedEdge e) {
        int v = e.from();
        int w = e.to();

        if (distTo[w] > distTo[v] + e.weight()) {
            distTo[w] = distTo[v] + e.weight();
            edgeTo[w] = e;
        }
    }

    // 顶点松弛
    private void relax(EdgeWeightedDigraph G, int v) {
        // v指出的边
        for (DirectedEdge e : G.adj(v)) {
            int w = e.to();
            if (distTo[w] > distTo[v] + e.weight()) {
                distTo[w] = distTo[v] + e.weight();
                edgeTo[w] = e;
                trace.addNewLink(new TraceLink(v, w, String.valueOf(e.weight())));

                // v指向顶点是否在优先队列中
                if (pq.contains(w)) {
                    pq.changeKey(w, distTo[w]); // 降低优先级
                } else {
                    pq.insert(w, distTo[w]); // 加入
                }
            }
        }
    }


    @Override
    public EdgeWeightedDigraph G() {
        return G;
    }

    @Override
    public int s() {
        return s;
    }

    @Override
    public double distTo(int v) {
        return distTo[v];
    }

    @Override
    public boolean hasPathTo(int v) {
        return distTo[v] < Double.POSITIVE_INFINITY;
    }

    @Override
    public Iterable<DirectedEdge> pathTo(int v) {
        if (!this.hasPathTo(v)) {
            return null;
        }

        Stack<DirectedEdge> path = new Stack<>();
        for (DirectedEdge e = edgeTo[v]; e != null; e = edgeTo[e.from()]) { // edgeTo[s] == null
            path.push(e);
        }
        return path;
    }

    @Override
    public Trace trace() {
        return trace;
    }
}
