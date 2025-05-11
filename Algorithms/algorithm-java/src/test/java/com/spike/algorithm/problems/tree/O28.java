package com.spike.algorithm.problems.tree;


// 对称的二叉树
public class O28 {

    public static void main(String[] args) {
        O28 o28 = new O28();

        TreeNode root = new TreeNode(8,
                new TreeNode(6,
                        new TreeNode(5),
                        new TreeNode(7)),
                new TreeNode(6,
                        new TreeNode(7),
                        new TreeNode(5)));
        System.out.println(o28.isSymmetrical(root, root)); // true

        TreeNode root2 = new TreeNode(8,
                new TreeNode(6,
                        new TreeNode(5),
                        new TreeNode(7)),
                new TreeNode(9,
                        new TreeNode(7),
                        new TreeNode(5)));
        System.out.println(o28.isSymmetrical(root2, root2)); // false


        TreeNode root3 = new TreeNode(7,
                new TreeNode(7,
                        new TreeNode(7),
                        new TreeNode(7)),
                new TreeNode(7,
                        new TreeNode(7),
                        null));
        System.out.println(o28.isSymmetrical(root3, root3)); // false

    }

    public boolean isSymmetrical(TreeNode r1, TreeNode r2) {
        if (r1 == null && r2 == null) {
            return true;
        }
        if (r1 == null || r2 == null) {
            return false;
        }
        if (r1.val != r2.val) {
            return false;
        }

        // r1: 先序遍历
        // r2: 对称的先序遍历
        return this.isSymmetrical(r1.left, r2.right) && this.isSymmetrical(r1.right, r2.left);
    }
}
