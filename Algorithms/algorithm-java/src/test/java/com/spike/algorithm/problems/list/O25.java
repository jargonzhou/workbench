package com.spike.algorithm.problems.list;

// 合并两个排序的链表
public class O25 {
    public static void main(String[] args) {
        O25 o25 = new O25();

        ListNode list1 = new ListNode(1, new ListNode(3, new ListNode(5, new ListNode(7))));
        ListNode list2 = new ListNode(2, new ListNode(4, new ListNode(6, new ListNode(8))));

        ListNode result = o25.merge(list1, list2);
        // 1 2 3 4 5 6 7 8
        ListNode.traverse(result);
    }

    public ListNode merge(ListNode list1, ListNode list2) {
        if (list1 == null) {
            return list2;
        }
        if (list2 == null) {
            return list1;
        }

        ListNode result = null;
        if (list1.val < list2.val) {
            result = list1;
            result.next = this.merge(list1.next, list2);
        } else {
            result = list2;
            result.next = this.merge(list1, list2.next);
        }
        return result;
    }
}
