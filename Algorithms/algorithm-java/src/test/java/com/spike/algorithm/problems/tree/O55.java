package com.spike.algorithm.problems.tree;

// 二叉树的深度
public class O55 {
    public static void main(String[] args) {
        O55 o55 = new O55();

        TreeNode root = new TreeNode(1,
                new TreeNode(2,
                        new TreeNode(4),
                        new TreeNode(5,
                                new TreeNode(7),
                                null)),
                new TreeNode(3,
                        null,
                        new TreeNode(6)));

        int depth = o55.depth(root);
        // 4
        System.out.println(depth);

        boolean balanced = o55.isBalanced(root);
        // true
        System.out.println(balanced);
    }

    public int depth(TreeNode x) {
        if (x == null) {
            return 0;
        }
        // 左右的最大子树深度 + 1
        return Math.max(this.depth(x.left), this.depth(x.right)) + 1;
    }

    // 判断二叉树是否平衡的
    public boolean isBalanced(TreeNode x) {
        return this.depthForBalanced(x) != -1;
    }

    private int depthForBalanced(TreeNode x) {
        if (x == null) {
            return 0;
        }
        // 使用后序遍历: 左/右子树不平衡, 则不平衡
        int left = this.depthForBalanced(x.left);
        if (left == -1) {
            return -1;
        }
        int right = this.depthForBalanced(x.right);
        if (right == -1) {
            return -1;
        }

        // 使用-1表示不平衡
        return Math.abs(left - right) > 1 ? -1 : 1 + Math.max(left, right);
    }
}
