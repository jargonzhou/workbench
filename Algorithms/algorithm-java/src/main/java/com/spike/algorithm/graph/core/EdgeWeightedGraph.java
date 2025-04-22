package com.spike.algorithm.graph.core;


import com.spike.algorithm.adt.Bag;

/**
 * 加权图.
 */
public class EdgeWeightedGraph implements IWeightedGraph {

    private final int V;
    private int E;
    private Bag<Edge>[] adj;

    @SuppressWarnings("unchecked")
    public EdgeWeightedGraph(int V) {
        this.V = V;
        this.E = 0;
        this.adj = (Bag<Edge>[]) new Bag[V];
        for (int v = 0; v < V; v++) {
            adj[v] = new Bag<>();
        }
    }

    @Override
    public int V() {
        return V;
    }

    @Override
    public int E() {
        return E;
    }

    @Override
    public void addEdge(Edge edge) {
        int v = edge.either();
        int w = edge.other(v);
        adj[v].add(edge);
        adj[w].add(edge);
        E++;
    }

    @Override
    public Iterable<Edge> adj(int v) {
        return adj[v];
    }

    @Override
    public Iterable<Edge> edges() {
        Bag<Edge> edges = new Bag<>();
        for (int v = 0; v < V; v++) {
            for (Edge e : adj[v]) {
                if (e.other(v) > v) {// 去除重复
                    edges.add(e);
                }
            }
        }
        return edges;
    }

    @Override
    public String dump(boolean sep) {
        StringBuilder sb = new StringBuilder();
        for (int v = 0; v < V; v++) {
            Bag<Edge> bag = adj[v];
            for (Edge e : bag) {
                int from = e.either();
                sb.append("ae " + from + " " + e.other(from)).append(System.lineSeparator());
                sb.append("le " + from + " " + e.other(from) + " " + e.weight()).append(System.lineSeparator());
                if (sep) {
                    sb.append("ns").append(System.lineSeparator());
                }
            }
        }
        return sb.toString();
    }
}
