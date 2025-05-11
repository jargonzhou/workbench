package com.spike.algorithm.problems.tree;

// 二叉搜索树的第k大节点
public class O54 {
    private int k;

    public static void main(String[] args) {
        O54 o54 = new O54();

        TreeNode root = new TreeNode(5,
                new TreeNode(3,
                        new TreeNode(2),
                        new TreeNode(4)),
                new TreeNode(7,
                        new TreeNode(6),
                        new TreeNode(8)));
        // 2 3 4 5 6 7 8
        TreeNode.in(root);
        System.out.println();

        o54.k = 3;
        TreeNode result = o54.kth(root);
        // 4
        if (result != null) {
            System.out.println(result.val);
        }
    }


    public TreeNode kth(TreeNode x) {
        if (x == null || k == 0) { // k == 0时
            return null;
        }

        return this.doKth(x);
    }

    private TreeNode doKth(TreeNode x) {
        // 中序遍历
        TreeNode result = null;
        if (x.left != null) {
            result = this.doKth(x.left);
        }

        if (result == null) {
            if (k == 1) { // k == 1时
                result = x;
            }
            k--;
        }

        if (result == null && x.right != null) {
            result = this.doKth(x.right);
        }

        return result;
    }


}
