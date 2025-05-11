package com.spike.algorithm.problems.list;

// 链表中环的入口节点
public class O23 {

    public static void main(String[] args) {
        O23 o23 = new O23();

        ListNode n1 = new ListNode(1);
        ListNode n2 = new ListNode(2);
        ListNode n3 = new ListNode(3);
        ListNode n4 = new ListNode(4);
        ListNode n5 = new ListNode(5);
        ListNode n6 = new ListNode(6);
        n1.next = n2;
        n2.next = n3;
        n3.next = n4;
        n4.next = n5;
        n5.next = n6;
        n6.next = n3;

        // 方法1: 辅助Set

        // 双指针法
        ListNode result = o23.entryNodeOfLoop(n1);
        // 3
        if (result != null) {
            System.out.print(result.val);
        }
    }

    public ListNode entryNodeOfLoop(ListNode x) {
        ListNode meetingNode = this.meetingNode(x);
        if (meetingNode == null) { // 无环
            return null;
        }

        int n = 1; // 环中节点数量
        ListNode t = meetingNode;
        while (t.next != meetingNode) {
            t = t.next;
            n++;
        }

        // 双指针
        ListNode p1 = x;
        // p1先走n步
        for (int i = 0; i < n; i++) {
            p1 = p1.next;
        }
        // 再同时移动p1和p2
        // 非环长度m
        // p1: n + m
        // p2: m
        ListNode p2 = x;
        while (p1 != p2) { // 直到相遇
            p1 = p1.next;
            p2 = p2.next;
        }

        return p1;
    }

    // 快慢指针在环中相遇的节点
    private ListNode meetingNode(ListNode x) {
        if (x == null) {
            return null;
        }

        // 快慢指针: 快的走2步, 慢的走1步
        // 如果走的快的到链表末尾, 没有追上慢指针: 无环
        ListNode slow = x.next;
        if (slow == null) {
            return null;
        }
        ListNode fast = slow.next;

        while (fast != null && slow != null) {
            if (fast == slow) { // 相遇
                return fast;
            }

            fast = fast.next;
            if (fast != null) {
                fast = fast.next;
            }
            slow = slow.next;
        }

        return null;
    }
}
