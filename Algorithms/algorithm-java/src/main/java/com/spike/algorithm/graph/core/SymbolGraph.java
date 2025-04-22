package com.spike.algorithm.graph.core;


import com.spike.algorithm.searching.SequentialSearchST;
import com.spike.algorithm.searching.core.ST;

/**
 * 符号图: 顶点名称为字符串.
 * <p>
 * 使用符号表, 记录顶点名称与顶点编号之间的对应关系.
 */
public class SymbolGraph {

    private ST<String, Integer> st; // 符号表: 顶点名称 -> 顶点编号
    private String[] keys; // 顶点的名称, 索引: 顶点, 值: 顶点名称
    private Graph G; // 内部的图

    public SymbolGraph(String stream, String sep) {
        st = new SequentialSearchST<>();
        String[] inputKeys = stream.split(sep);
        for (String inputKey : inputKeys) {
            if (!st.contains(inputKey)) {
                st.put(inputKey, st.size());
            }
        }
        keys = new String[st.size()];
        for (String name : st.keys()) {
            keys[st.get(name)] = name;
        }
        G = new Graph(st.size());
    }

    public void addEdge(String source, String target) {
        if (!this.contains(source)) {
            throw new IllegalStateException("Vertex source not exist!");
        }
        if (!this.contains(target)) {
            throw new IllegalStateException("Vertex target not exist!");
        }

        G.addEdge(st.get(source), st.get(target));
    }

    /**
     * 是否包含顶点名称.
     */
    public boolean contains(String name) {
        return st.contains(name);
    }

    /**
     * 顶点名称对应的顶点编号.
     */
    public int index(String name) {
        return st.get(name);
    }

    /**
     * 顶点编号对应的顶点名称.
     */
    public String name(int v) {
        return keys[v];
    }

    /**
     * 内部的图.
     */
    public Graph G() {
        return G;
    }

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
        for (int v = 0; v < G.V(); v++) {
            Iterable<Integer> bag = G.adj(v);
            for (Integer w : bag) {
                sb.append("ae " + name(v) + " " + name(w)).append(System.lineSeparator());
                if (sep) {
                    sb.append("ns").append(System.lineSeparator());
                }
            }
        }
        return sb.toString();
    }
}
