package com.spike.algorithm.problems.tree;

import java.util.LinkedList;

// 二叉树中和为某一值的路径
public class O34 {
    public static void main(String[] args) {
        O34 o34 = new O34();

        TreeNode root = new TreeNode(10,
                new TreeNode(5,
                        new TreeNode(4),
                        new TreeNode(7)),
                new TreeNode(12));
        int expectedSum = 22;
        LinkedList<TreeNode> path = new LinkedList<>();

        // 10 5 7
        // 10 12
        o34.FindPath(root, expectedSum, path, 0);
    }

    public void FindPath(TreeNode x, int expectedSum, LinkedList<TreeNode> path, int currentSum) {
        if (x == null) {
            return;
        }
        currentSum += x.val; // 先序遍历
        path.addLast(x); // 加入末尾

        if (x.left == null && x.right == null) { // 叶子节点
            if (currentSum == expectedSum) {
                for (TreeNode n : path) {
                    System.out.print(n.val + " ");
                }
                System.out.println();
            }
        } else {
            // 遍历子节点
            if (x.left != null) {
                this.FindPath(x.left, expectedSum, path, currentSum);
            }
            if (x.right != null) {
                this.FindPath(x.right, expectedSum, path, currentSum);
            }
        }

        // 返回父节点: 移除当前节点
        path.removeLast(); // 从末尾删除
//        currentSum -= x.val; // 没必要
    }
}
