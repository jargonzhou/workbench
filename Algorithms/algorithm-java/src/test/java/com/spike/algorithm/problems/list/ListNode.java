package com.spike.algorithm.problems.list;

public class ListNode {
    int val = 0;
    ListNode next;

    public ListNode(int val) {
        this.val = val;
    }

    public ListNode(int val, ListNode next) {
        this.val = val;
        this.next = next;
    }

    public static void traverse(ListNode x) {
        if (x == null) {
            System.out.println();
            return;
        }

        while (x != null) {
            System.out.print(x.val + " ");
            x = x.next;
        }
        System.out.println();
    }
}
