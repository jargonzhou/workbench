package com.spike.algorithm.problems.tree;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Stack;

// 从上往下打印二叉树
public class O32 {

    public static void main(String[] args) {
        O32 o32 = new O32();
        TreeNode root = new TreeNode(8,
                new TreeNode(6, new TreeNode(5), new TreeNode(7)),
                new TreeNode(10, new TreeNode(9), new TreeNode(11)));

        // 8 6 10 5 7 9 11
        o32.PrintFromTopToBottom(root);

        // 8
        // 6 10
        // 5 7 9 11
        o32.PrintFromTopToBottomLineByLine(root);

        TreeNode root2 = new TreeNode(1,
                new TreeNode(2,
                        new TreeNode(4,
                                new TreeNode(8),
                                new TreeNode(9)),
                        new TreeNode(5,
                                new TreeNode(10),
                                new TreeNode(11))),
                new TreeNode(3,
                        new TreeNode(6,
                                new TreeNode(12),
                                new TreeNode(13)),
                        new TreeNode(7,
                                new TreeNode(14),
                                new TreeNode(15))));

        // 1
        // 3 2
        // 4 5 6 7
        // 15 14 13 12 11 10 9 8
        o32.PrintFromTopToBottomZ(root2);
    }

    public void PrintFromTopToBottom(TreeNode x) {
        if (x == null) {
            return;
        }

        // 队列
        Queue<TreeNode> queue = new LinkedList<>();
        queue.add(x);

        while (!queue.isEmpty()) {
            // 先序遍历
            TreeNode head = queue.remove();
            System.out.print(head.val + " ");

            if (head.left != null) {
                queue.add(head.left);
            }
            if (head.right != null) {
                queue.add(head.right);
            }
        }
        System.out.println();
    }

    // 分行从上到下打印二叉树
    public void PrintFromTopToBottomLineByLine(TreeNode x) {
        if (x == null) {
            return;
        }

        Queue<TreeNode> queue = new LinkedList<>();
        queue.add(x);
        int currentLevelLeftCount = 1; // 当前层未打印节点数量
        int nextLevelCount = 0; // 下层节点数量

        while (!queue.isEmpty()) {
            // 先序遍历
            TreeNode head = queue.remove();
            System.out.print(head.val + " ");

            if (head.left != null) {
                queue.add(head.left);
                nextLevelCount++;
            }
            if (head.right != null) {
                queue.add(head.right);
                nextLevelCount++;
            }

            --currentLevelLeftCount;
            if (currentLevelLeftCount == 0) {
                System.out.println();
                currentLevelLeftCount = nextLevelCount; // 开始下一层
                nextLevelCount = 0;
            }

        }
        System.out.println();
    }

    // 之字形打印二叉树
    public void PrintFromTopToBottomZ(TreeNode x) {
        if (x == null) {
            return;
        }

        // 两个栈
        Stack<TreeNode>[] stacks = new Stack[2];
        stacks[0] = new Stack<>();
        stacks[1] = new Stack<>();
        int currentLevel = 0;
        int nextLevel = 1;

        stacks[currentLevel].push(x);
        while (!stacks[currentLevel].isEmpty() || !stacks[nextLevel].isEmpty()) {
            // 先序遍历
            TreeNode top = stacks[currentLevel].pop();
            System.out.print(top.val + " ");

            if (currentLevel == 0) { // ->: next level <-
                if (top.left != null) {
                    stacks[nextLevel].push(top.left); // 左
                }
                if (top.right != null) {
                    stacks[nextLevel].push(top.right); // 右
                }
            } else { // <-: next level ->
                if (top.right != null) {
                    stacks[nextLevel].push(top.right); // 右
                }
                if (top.left != null) {
                    stacks[nextLevel].push(top.left); // 左
                }
            }

            if (stacks[currentLevel].isEmpty()) { // current level done
                System.out.println();
                currentLevel = 1 - currentLevel;
                nextLevel = 1 - nextLevel;
            }
        }
    }

}
