package com.spike.algorithm.graph.core;


import com.spike.algorithm.adt.Bag;

/**
 * 有向图.
 */
public class Digraph implements IGraph {

    private final int V; // 顶点的数量
    private int E; // 边的数量
    private Bag<Integer>[] adj;// 邻接表

    /**
     * 构造有向图.
     */
    @SuppressWarnings("unchecked")
    public Digraph(int V) {
        this.V = V;
        this.E = 0;
        this.adj = (Bag<Integer>[]) new Bag[V];
        for (int v = 0; v < V; v++) {
            adj[v] = new Bag<Integer>();
        }
    }

    /**
     * 顶点的数量.
     */
    @Override
    public int V() {
        return V;
    }

    /**
     * 边的数量.
     */
    @Override
    public int E() {
        return E;
    }

    /**
     * 添加由v指向w的边.
     */
    @Override
    public void addEdge(int v, int w) {
        adj[v].add(w);
        E++;
    }

    /**
     * 由顶点v指出的边另一端顶点.
     */
    @Override
    public Iterable<Integer> adj(int v) {
        return adj[v];
    }

    @Override
    public String dump(boolean sep) {
        StringBuilder sb = new StringBuilder();

//# action2method = {
//# 	'ns' : self.next_step,       # 下一步
//# 	'an' : self.add_node,        # 添加节点
//# 	'hn' : self.highlight_node,  # 高亮节点
//# 	'ln' : self.label_node,      # 添加节点标签
//# 	'un' : self.unlabel_node,    # 移除节点标签
//# 	'rn' : self.remove_node,     # 删除节点
//# 	'ae' : self.add_edge,        # 添加边
//# 	'he' : self.highlight_edge,  # 高亮边
//# 	'le' : self.label_edge,      # 添加边标签
//# 	'ue' : self.unlabel_edge,    # 移除边标签
//# 	're' : self.remove_edge,     # 删除边
//# }
//#
//# https://github.com/mapio/GraphvizAnim/blob/master/gvanim/__main__.py
        for (int v = 0; v < V; v++) {
            Bag<Integer> bag = adj[v];
            for (Integer w : bag) {
                sb.append("ae " + v + " " + w).append(System.lineSeparator());
                if (sep) {
                    sb.append("ns").append(System.lineSeparator());
                }
            }
        }

        return sb.toString();
    }

    /**
     * 图的逆.
     */
    public Digraph reverse() {
        Digraph R = new Digraph(V);

        for (int v = 0; v < V; v++) {
            for (int w : this.adj(v)) {
                R.addEdge(w, v); // 逆向的边
            }
        }

        return R;
    }

}
