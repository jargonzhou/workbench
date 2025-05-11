package com.spike.algorithm.problems.list;

import java.util.Stack;

// 从尾到头打印链表
public class O6 {
    public static void main(String[] args) {
        O6 o6 = new O6();

        ListNode list = new ListNode(1, new ListNode(2, new ListNode(3)));

        // 3 2 1
        o6.reversePrint(list);

        // 3 2 1
        o6.reversePrintRecursively(list);
        System.out.println();
    }

    // 使用栈
    public void reversePrint(ListNode x) {
        Stack<ListNode> stack = new Stack<>();
        while (x != null) {
            stack.push(x);
            x = x.next;
        }

        while (!stack.isEmpty()) {
            System.out.print(stack.pop().val + " ");
        }
        System.out.println();
    }

    // 递归
    public void reversePrintRecursively(ListNode x) {
        if (x != null) {
            // 先打印后续节点
            reversePrintRecursively(x.next);

            // 再打印当前节点
            System.out.print(x.val + " ");
        }
    }

    // 或者: 反转链表, 见O24
}
