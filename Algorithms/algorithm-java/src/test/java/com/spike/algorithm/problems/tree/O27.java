package com.spike.algorithm.problems.tree;

// 二叉树的镜像
public class O27 {

    public static void main(String[] args) {
        O27 o27 = new O27();

        TreeNode root = new TreeNode(8,
                new TreeNode(6,
                        new TreeNode(5),
                        new TreeNode(7)),
                new TreeNode(10,
                        new TreeNode(9),
                        new TreeNode(11)));

        // 8 6 10 5 7 9 11
        TreeNode.level(root);
        System.out.println();

        o27.mirror(root);

        // 8 10 6 11 9 7 5
        TreeNode.level(root);
        System.out.println();
    }

    public void mirror(TreeNode x) {
        if (x == null) {
            return;
        }

        if (x.left == null && x.right == null) {
            return;
        }

        // 先序遍历
        // 交换左右子树
        TreeNode temp = x.right;
        x.right = x.left;
        x.left = temp;

        if (x.left != null) {
            this.mirror(x.left);
        }
        if (x.right != null) {
            this.mirror(x.right);
        }
    }
}
