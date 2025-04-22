package com.spike.algorithm.graph.core;

/**
 * 带权重边的有向图接口.
 */
public interface IWeightedDigraph {

    /**
     * 顶点数量.
     */
    int V();

    /**
     * 边数量.
     */
    int E();

    /**
     * 添加由顶点v和w构成的边.
     */
    void addEdge(DirectedEdge edge);

    /**
     * 获取顶点v指出的边.
     */
    Iterable<DirectedEdge> adj(int v);

    /**
     * 图中所有有向边.
     */
    Iterable<DirectedEdge> edges();

    String dump(boolean sep);
}
