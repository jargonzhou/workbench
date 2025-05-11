package com.spike.algorithm.problems.list;

// 反转链表
public class O24 {
    public static void main(String[] args) {
        O24 o24 = new O24();

        ListNode list = new ListNode(1, new ListNode(2, new ListNode(3)));
        // 1 2 3
        ListNode.traverse(list);

        ListNode reversed = o24.reverse(list);
        // 3 2 1
        ListNode.traverse(reversed);
    }

    public ListNode reverse(ListNode x) {
        if (x == null) {
            return x;
        }

        ListNode prev = null; // 翻转过程中前一个节点
        while (x != null) {
            ListNode next = x.next; // 当前节点的下一个节点

            x.next = prev; // 反向连接
            // 步进
            prev = x;
            x = next;
        }
        return prev;
    }
}
