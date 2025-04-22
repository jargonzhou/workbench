package com.spike.algorithm.support.trace;

import java.util.Optional;

public class TraceNode {
    private final int node;
    private String label;

    public TraceNode(int node) {
        this.node = node;
        this.label = String.valueOf(node);
    }

    public TraceNode(int node, String label) {
        this.node = node;
        this.label = Optional.ofNullable(label).orElse(String.valueOf(node));
    }

    public int node() {
        return node;
    }

    public String label() {
        return label;
    }

    public void label(String label) {
        this.label = label;
    }
}