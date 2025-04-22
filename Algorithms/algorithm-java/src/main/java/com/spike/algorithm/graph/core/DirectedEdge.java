package com.spike.algorithm.graph.core;

/**
 * 加权有向边.
 */
public class DirectedEdge {
    private final int v; // 起点
    private final int w; // 终点
    private final double weight; // 权重

    public DirectedEdge(int v, int w, double weight) {
        this.v = v;
        this.w = w;
        this.weight = weight;
    }

    public int from() {
        return v;
    }

    public int to() {
        return w;
    }

    public double weight() {
        return weight;
    }
}
