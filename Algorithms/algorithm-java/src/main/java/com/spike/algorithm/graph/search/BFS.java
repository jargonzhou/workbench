package com.spike.algorithm.graph.search;


import com.spike.algorithm.adt.Queue;
import com.spike.algorithm.graph.core.Edge;
import com.spike.algorithm.graph.core.IGraph;
import com.spike.algorithm.support.trace.Trace;
import com.spike.algorithm.support.trace.Traceable;

/**
 * 广度优先搜索((Breadth First Search, BFS).
 *
 * <pre>
 * 实现:
 *
 * 使用FIFO队列保存所有已经标记过的但其邻接顶点未被检查过的顶点;
 * 将开始顶点s加入队列, 重复执行直到队列为空: (1) 取队列中下一个顶点v并标记它, (2) 将v的所有未标记的邻接顶点加入队列.
 * </pre>
 */
public class BFS<GRAPH extends IGraph> implements IBFS<GRAPH>, Traceable {

    private boolean[] marked; // 顶点是否访问过, 索引: 顶点
    private final Trace trace = new Trace();

    public BFS(GRAPH G, int s) {
        this.marked = new boolean[G.V()];

        this.bfs(G, s);
    }

    @Override
    public void bfs(GRAPH G, int s) {
        Queue<Integer> q = new Queue<>();
        marked[s] = true;
        q.enqueue(s); // 入队

        while (!q.isEmpty()) {
            int v = q.dequeue(); // 出队
            // System.err.println("DEBUG>>> dequeue " + v + ", Queue=" + q);

            for (int w : G.adj(v)) {
                if (!marked[w]) {
                    trace.add(new Edge(v, w));
                    marked[w] = true;
                    q.enqueue(w); // 入队
                }
            }
        }
    }

    @Override
    public Trace trace() {
        return trace;
    }
}
