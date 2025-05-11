package com.spike.algorithm.problems.list;

// 两个链表的第一个公共节点
public class O52 {
    public static void main(String[] args) {
        O52 o52 = new O52();

        // 单链表: 重合后, 后续节点均相同, 即Y状
        ListNode common = new ListNode(6,
                new ListNode(7));
        ListNode list1 = new ListNode(1,
                new ListNode(2,
                        new ListNode(3,
                                common)));
        ListNode list2 = new ListNode(4,
                new ListNode(5,
                        common));

        ListNode firstCommon = o52.firstCommon(list1, list2);
        // 6
        if (firstCommon != null) {
            System.out.println(firstCommon.val);
        }
    }

    public ListNode firstCommon(ListNode list1, ListNode list2) {
        if (list1 == null || list2 == null) {
            return null;
        }

        int length1 = 0;
        int length2 = 0;
        ListNode head1 = list1;
        ListNode head2 = list2;
        while (head1 != null) {
            length1++;
            head1 = head1.next;
        }
        while (head2 != null) {
            length2++;
            head2 = head2.next;
        }

        // 长链表先走
        int step = length1 - length2;
        if (step > 0) {
            while (step != 0) {
                list1 = list1.next;
                step--;
            }
        } else {
            while (step != 0) {
                list2 = list2.next;
                step++;
            }
        }

        while (list1 != null && list2 != null) {
            if (list1 == list2) { // 相等时返回
                return list1;
            } else {
                list1 = list1.next;
                list2 = list2.next;
            }
        }

        return null;
    }

}
