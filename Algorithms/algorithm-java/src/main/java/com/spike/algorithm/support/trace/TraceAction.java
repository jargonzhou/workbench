package com.spike.algorithm.support.trace;

public class TraceAction {
    private final TraceStep step;
    private TraceLink link;
    private TraceNode node;

    public static final TraceAction ns = new TraceAction(TraceStep.ns);

    public static TraceAction he(int from, int to) {
        return new TraceAction(TraceStep.he, new TraceLink(from, to));
    }

    public TraceAction(TraceStep step) {
        this.step = step;
    }

    public TraceAction(TraceStep step, TraceLink link) {
        this.step = step;
        this.link = link;
    }

    public TraceAction(TraceStep step, TraceNode node) {
        this.step = step;
        this.node = node;
    }

    public String dump() {
        StringBuilder sb = new StringBuilder();
        switch (step) {
            case ns:
                sb.append(step.name());
                break;
            case an:
            case hn:
            case rn:
            case un:
                sb.append(step.name() + " " + node.node());
                break;
            case ln:
                sb.append(step.name() + " " + node.node() + " " + node.label());
                break;
            case ae:
            case he:
            case re:
            case ue:
                sb.append(step.name() + " " + link.from().node() + " " + link.to().node());
                break;
            case le:
                sb.append(step.name() + " " + link.from().node() + " " + link.to().node() + " " + link.label());
                break;
        }

        sb.append(System.lineSeparator());

        return sb.toString();
    }
}