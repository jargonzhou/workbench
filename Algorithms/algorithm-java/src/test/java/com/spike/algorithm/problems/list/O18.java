package com.spike.algorithm.problems.list;

// 删除链表的节点
// 修改: 返回删除后的链表的头节点
public class O18 {
    public static void main(String[] args) {
        O18 o18 = new O18();

        ListNode list = new ListNode(1, new ListNode(2, new ListNode(3)));
        // 1 2 3
        ListNode.traverse(list);

        ListNode result = o18.deleteNode(list, 2);
        // 1 3
        ListNode.traverse(result);

        // 删除链表中值重复的节点
        ListNode list2 = new ListNode(1, new ListNode(2, new ListNode(3, new ListNode(3,
                new ListNode(4, new ListNode(4, new ListNode(5)))))));
        // 1 2 3 3 4 4 5
        ListNode.traverse(list2);
        ListNode result2 = o18.deleteDuplication(list2);
        // 1 2 5
        ListNode.traverse(result2);
    }

    public ListNode deleteNode(ListNode x, int val) {
        if (x == null) {
            return null;
        }
        if (x.val == val) {
            return x.next;
        }

        // 新建头节点: 待删除节点的前一个节点
        ListNode prev = new ListNode(-1);
        prev.next = x;

        ListNode current = x;
        ListNode next = null;
        while (current != null) {
            current = current.next;
            prev = prev.next;

            if (current.val == val) { // 如果相等, 将指针指向下一个节点
                next = current.next;
                break;
            }
        }
        current.next = null; // 移除当前节点的nxt链接
        prev.next = next; // 将前一个几点直接连接到有一个节点

        return x;
    }

    // 在已排序的链表中, 删除重复的节点
    // 方法1: 使用LinkedHashMap
    // 方法2: 原地删除
    public ListNode deleteDuplication(ListNode x) {
        // 创建头节点
        ListNode head = new ListNode(-1);
        head.next = x;

        ListNode prev = head;
        ListNode current = x;
        while (current != null) {
            // 移除与下一个节点值相同的
            if (current.next != null && current.val == current.next.val) {
                current = current.next;
                while (current.next != null && current.val == current.next.val) {
                    current = current.next;
                }

                // 步进
                current = current.next; // 需要过滤掉最后一个值相同的节点
                prev.next = current;
            } else {
                prev = current;
                current = current.next;
            }
        }

        return head.next;
    }
}
