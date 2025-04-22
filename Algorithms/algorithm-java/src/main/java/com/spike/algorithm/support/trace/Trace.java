package com.spike.algorithm.support.trace;

import com.google.common.base.Strings;
import com.google.common.collect.Lists;
import com.spike.algorithm.graph.core.Edge;

import java.util.List;

public class Trace {
    @Deprecated
    private List<Edge> edges = Lists.newArrayList();
    private final List<TraceAction> actions = Lists.newArrayList();
    private TraceOptions traceOptions = new TraceOptions();
    private int linkSequence = 1;

    public Trace() {
    }

    public Trace(TraceOptions traceOptions) {
        this.traceOptions = traceOptions;
    }

    public void add(TraceAction action) {
        actions.add(action);
    }

    public void add(List<TraceAction> actions) {
        this.actions.addAll(actions);
    }

    public void add(Edge edge) {
        edges.add(edge);
    }

    public static class TraceOptions {
        // 标记顶点已访问
        private boolean markVisitNode = true;
        // 标记链接序号
        private boolean labelLinkSequence = true;

        public TraceOptions() {
        }

        public boolean isMarkVisitNode() {
            return markVisitNode;
        }

        public void setMarkVisitNode(boolean markVisitNode) {
            this.markVisitNode = markVisitNode;
        }

        public boolean isLabelLinkSequence() {
            return labelLinkSequence;
        }

        public void setLabelLinkSequence(boolean labelLinkSequence) {
            this.labelLinkSequence = labelLinkSequence;
        }
    }

    // with source
    @Deprecated
    public String dump() {
        StringBuilder sb = new StringBuilder();
        if (!edges.isEmpty()) {
            int index = 1;
            for (Edge e : edges) {
                int v = e.either();
                int w = e.other(v);
                sb.append("hn " + w).append(System.lineSeparator());
                sb.append("ln " + w + " \"" + w + "(v)\"").append(System.lineSeparator());
                sb.append(e.dump(String.valueOf(index++))).append(System.lineSeparator());
                sb.append("ns").append(System.lineSeparator());
            }
        }
        return sb.toString();
    }

    public String dumpTrace() {
        StringBuilder sb = new StringBuilder();
        if (!actions.isEmpty()) {
            for (TraceAction action : actions) {
                sb.append(action.dump());
            }
        }
        return sb.toString();
    }

    public void addNewLink(TraceLink link) {
        TraceNode to = link.to();
        actions.add(new TraceAction(TraceStep.hn, to));
        if (traceOptions.isMarkVisitNode()) {
            to.label("\"" + Strings.nullToEmpty(to.label()) + "(v)\"");
        }
        actions.add(new TraceAction(TraceStep.ln, to));

        actions.add(new TraceAction(TraceStep.he, link));
        if (traceOptions.isLabelLinkSequence()) {
            link.label("\"" + Strings.nullToEmpty(link.label()) + " (" + linkSequence + ")\"");
            linkSequence++;
        }
        actions.add(new TraceAction(TraceStep.le, link));


        actions.add(new TraceAction(TraceStep.ns));
    }


    @Deprecated
    public String dumpWithoutSource() {
        StringBuilder sb = new StringBuilder();
        if (!edges.isEmpty()) {
            int index = 1;
            for (Edge e : edges) {
                int v = e.either();
                int w = e.other(v);
                sb.append("hn " + v).append(System.lineSeparator());
                sb.append("hn " + w).append(System.lineSeparator());
                sb.append("ln " + v + " \"" + v + "(v)\"").append(System.lineSeparator());
                sb.append("ln " + w + " \"" + w + "(v)\"").append(System.lineSeparator());
                sb.append(e.dump(String.valueOf(index++))).append(System.lineSeparator());
                sb.append("ns").append(System.lineSeparator());
            }
        }
        return sb.toString();
    }

    public TraceOptions getTraceOptions() {
        return traceOptions;
    }

    public void setTraceOptions(TraceOptions traceOptions) {
        this.traceOptions = traceOptions;
    }
}
