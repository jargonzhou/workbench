package com.spike.algorithm.graph.search.dfs;

import com.spike.algorithm.graph.core.Digraph;
import com.spike.algorithm.graph.search.dfs.cycle.DirectedCycleDetection;

/**
 * 有向图上的拓扑排序, 仅是有向无环图(DAG)时可排序.
 */
public class TopologicalSort {

    private Iterable<Integer> order; // 顶点排序

    public TopologicalSort(Digraph DG) {
        DirectedCycleDetection dcd = new DirectedCycleDetection(DG);
        if (!dcd.hasCycle()) { // 无环时
            DepthFirstOrder dfo = new DepthFirstOrder(DG);
            order = dfo.reversePost(); // 逆后序
        }
    }

    /**
     * 是否是有向无环图.
     */
    public boolean isDAG() {
        return order != null;
    }

    /**
     * 返回排序结果, 不可排序时返回null.
     */
    public Iterable<Integer> order() {
        return order;
    }
}
