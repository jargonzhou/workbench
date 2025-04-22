package com.spike.algorithm.support.trace;

public class TraceLink {
    private final TraceNode from;
    private final TraceNode to;
    private String label;

    public TraceLink(TraceNode from, TraceNode to) {
        this.from = from;
        this.to = to;
    }

    public TraceLink(TraceNode from, TraceNode to, String label) {
        this.from = from;
        this.to = to;
        this.label = label;
    }

    public TraceLink(int from, int to) {
        this.from = new TraceNode(from);
        this.to = new TraceNode(to);
    }

    public TraceLink(int from, int to, String label) {
        this.from = new TraceNode(from);
        this.to = new TraceNode(to);
        this.label = label;
    }

    public TraceNode from() {
        return from;
    }

    public TraceNode to() {
        return to;
    }

    public String label() {
        return label;
    }

    public void label(String label) {
        this.label = label;
    }
}