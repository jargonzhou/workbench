package com.spike.algorithm.graph.core;

import com.spike.algorithm.adt.Bag;

public class EdgeWeightedDigraph implements IWeightedDigraph {
    private final int V;
    private int E;
    private Bag<DirectedEdge>[] adj;

    public EdgeWeightedDigraph(int V) {
        this.V = V;
        this.E = 0;
        adj = new Bag[V];
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
    public void addEdge(DirectedEdge e) {
        adj[e.from()].add(e);
        E++;
    }

    @Override
    public Iterable<DirectedEdge> adj(int v) {
        return adj[v];
    }

    @Override
    public Iterable<DirectedEdge> edges() {
        Bag<DirectedEdge> bag = new Bag<>();
        for (int v = 0; v < V; v++) {
            for (DirectedEdge e : adj[v]) {
                bag.add(e);
            }
        }
        return bag;
    }

    @Override
    public String dump(boolean sep) {
        StringBuilder sb = new StringBuilder();
        for (int v = 0; v < V; v++) {
            Bag<DirectedEdge> bag = adj[v];
            for (DirectedEdge e : bag) {
                sb.append("ae " + e.from() + " " + e.to()).append(System.lineSeparator());
                sb.append("le " + e.from() + " " + e.to() + " " + e.weight()).append(System.lineSeparator());
                if (sep) {
                    sb.append("ns").append(System.lineSeparator());
                }
            }
        }
        return sb.toString();
    }
}
