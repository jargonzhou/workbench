package com.spike.algorithm.example.uf;

import com.spike.algorithm.support.trace.Traceable;

public interface IUF extends Traceable {
    /**
     * 触点的数量.
     */
    int N();

    /**
     * 在p和q之间添加一条连接.
     */
    void union(int p, int q);

    /**
     * p所在的连通分量的标识符.
     */
    int find(int p);

    /**
     * 如果p和q在同一个分量中返回true.
     */
    boolean connected(int p, int q);

    /**
     * 连通分量的数量.
     */
    int count();
}
