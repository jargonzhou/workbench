package com.spike.algorithm.problems.tree;

import java.util.LinkedList;
import java.util.Queue;

// 二叉树节点
public class TreeNode {
    int val = 0;
    TreeNode left = null;
    TreeNode right = null;

    // 父节点
    TreeNode parent = null;

    public TreeNode(int val) {
        this.val = val;
    }

    public TreeNode(int val, TreeNode left, TreeNode right) {
        this.val = val;
        this.left = left;
        this.right = right;
    }

    public static void pre(TreeNode x) {
        if (x == null) {
            return;
        }

        System.out.print(x.val + " "); //
        if (x.left != null) {
            pre(x.left);
        }
        if (x.right != null) {
            pre(x.right);
        }
    }

    public static void in(TreeNode x) {
        if (x == null) {
            return;
        }

        if (x.left != null) {
            in(x.left);
        }
        System.out.print(x.val + " "); //
        if (x.right != null) {
            in(x.right);
        }
    }

    public static void post(TreeNode x) {
        if (x == null) {
            return;
        }

        if (x.left != null) {
            post(x.left);
        }
        if (x.right != null) {
            post(x.right);
        }
        System.out.print(x.val + " "); //
    }

    public static void level(TreeNode x) {
        Queue<TreeNode> queue = new LinkedList<>();
        queue.add(x);

        while (!queue.isEmpty()) {
            TreeNode n = queue.remove();
            System.out.print(n.val + " ");
            if (n.left != null) {
                queue.add(n.left);
            }
            if (n.right != null) {
                queue.add(n.right);
            }
        }

    }
}
