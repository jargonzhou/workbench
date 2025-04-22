package com.spike.algorithm.graph.sp;

import com.spike.algorithm.graph.core.DirectedEdge;
import com.spike.algorithm.graph.core.EdgeWeightedDigraph;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class DijkstraAllPairsSP implements IMSP {
    private final EdgeWeightedDigraph G;

    private DijkstraSP[] all;

    public DijkstraAllPairsSP(EdgeWeightedDigraph G) {
        this.G = G;
        all = new DijkstraSP[G.V()];
        for (int v = 0; v < G.V(); v++) {
            all[v] = new DijkstraSP(G, v);
        }
    }

    @Override
    public EdgeWeightedDigraph G() {
        return G;
    }

    @Override
    public List<Integer> ss() {
        return IntStream.range(0, G.V()).boxed().collect(Collectors.toList());
    }

    @Override
    public double distTo(int s, int v) {
        return all[s].distTo(v);
    }

    @Override
    public boolean hasPathTo(int s, int v) {
        return all[s].hasPathTo(v);
    }

    @Override
    public Iterable<DirectedEdge> pathTo(int s, int v) {
        return all[s].pathTo(v);
    }
}
