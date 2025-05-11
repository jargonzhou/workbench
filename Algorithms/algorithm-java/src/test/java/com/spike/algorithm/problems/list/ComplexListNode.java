package com.spike.algorithm.problems.list;

import java.util.function.Consumer;
import java.util.function.Function;

public class ComplexListNode {
    int val = 0;
    ComplexListNode next;
    ComplexListNode random;

    public ComplexListNode(int val) {
        this.val = val;
    }

    public ComplexListNode(int val, ComplexListNode next) {
        this.val = val;
        this.next = next;
    }

    public static void traverse(ComplexListNode x, Function<Integer, String> f) {
        if (x == null) {
            System.out.println();
            return;
        }

        while (x != null) {
            System.out.print(f.apply(x.val));
            if (x.random != null) {
                System.out.print("[" + f.apply(x.random.val) + "]");
            }
            System.out.print(" ");
            x = x.next;
        }
        System.out.println();
    }

    public static void traverse(ComplexListNode x) {
        traverse(x, String::valueOf);
    }
}
