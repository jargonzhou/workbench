package com.spike.algorithm.problems.list;

// 链表中的倒数第k个节点
public class O22 {
    public static void main(String[] args) {
        O22 o22 = new O22();

        ListNode list = new ListNode(1,
                new ListNode(2,
                        new ListNode(3,
                                new ListNode(4,
                                        new ListNode(5,
                                                new ListNode(6))))));
        ListNode result = o22.kthToTail(list, 3);
        // 4 5 6
        ListNode.traverse(result);
        result = o22.kthToTail(list, 0);
        //
        ListNode.traverse(result);
        result = o22.kthToTail(list, 6);
        // 1 2 3 4 5 6
        ListNode.traverse(result);
        result = o22.kthToTail(list, 7);
        //
        ListNode.traverse(result);
    }


    public ListNode kthToTail(ListNode x, int k) {
        if (x == null || k <= 0) {
            return null;
        }

        // 双指针
        // 第一个: 先走k步
        ListNode first = x;
        while (k != 0) {
            if (first == null) { // 过早结束遍历
                return null;
            }
            first = first.next;
            k--;
        }

        // 一起走
        while (first != null) {
            first = first.next;
            x = x.next;
        }
        // fast指向null

        return x;
    }
}
