package com.spike.algorithm.example.uf;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.spike.algorithm.support.trace.Trace;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

public class IUFTest {
    @Test
    public void quickFind() {
        List<UFPair> pairs = this.create();
        Set<Integer> points = this.points(pairs);
        this.doTest(new QuickFindUF(points.size()), pairs);
    }

    @Test
    public void quickUnion() {
        List<UFPair> pairs = this.create();
        Set<Integer> points = this.points(pairs);
        this.doTest(new QuickUnionUF(points.size()), pairs);
    }

    @Test
    public void weightedQuickUnion() {
        List<UFPair> pairs = this.create();
        Set<Integer> points = this.points(pairs);
        this.doTest(new WeightedQuickUnionUF(points.size()), pairs);
    }

    @Test
    public void uf() {
        List<UFPair> pairs = this.create();
        Set<Integer> points = this.points(pairs);
        this.doTest(new UF(points.size()), pairs);
    }

    private void doTest(IUF uf, List<UFPair> pairs) {
        pairs.forEach(pair -> {
            int p = pair.p;
            int q = pair.q;
            if (uf.find(p) != uf.find(q)) {
                uf.union(p, q);
                System.out.println(p + " " + q);
            }
        });
        System.out.println(uf.count() + " components");

        Trace trace = uf.trace();
        System.out.println(trace.dumpTrace());
    }


    public Set<Integer> points(List<UFPair> pairs) {
        Set<Integer> points = Sets.newHashSet();
        pairs.forEach(pair -> {
            points.add(pair.p);
            points.add(pair.q);
        });
        return points;
    }

    public List<UFPair> create() {
        // tinyUF.txt
        return Lists.newArrayList(
                new UFPair(4, 3),
                new UFPair(3, 8),
                new UFPair(6, 5),
                new UFPair(9, 4),
                new UFPair(2, 1),
                new UFPair(8, 9),
                new UFPair(5, 0),
                new UFPair(7, 2),
                new UFPair(6, 1),
                new UFPair(1, 0),
                new UFPair(6, 7));
    }

    public static class UFPair {
        public int p;
        public int q;

        public UFPair() {
        }

        public UFPair(int p, int q) {
            this.p = p;
            this.q = q;
        }
    }
}
