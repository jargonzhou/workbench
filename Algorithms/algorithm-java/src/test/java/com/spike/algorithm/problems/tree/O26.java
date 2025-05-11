package com.spike.algorithm.problems.tree;

// 树的子结构
public class O26 {
    public static void main(String[] args) {
        O26 o26 = new O26();

        TreeNode t1 = new TreeNode(8,
                new TreeNode(8,
                        new TreeNode(9),
                        new TreeNode(2,
                                new TreeNode(4),
                                new TreeNode(7))),
                new TreeNode(7));

        TreeNode t2 = new TreeNode(8,
                new TreeNode(9),
                new TreeNode(2));

        boolean result = o26.hasSubTree(t1, t2);
        // true
        System.out.println(result);
    }

    public boolean hasSubTree(TreeNode t1, TreeNode t2) {
        boolean result = false;
        if (t1 != null && t2 != null) {
            if (t1.val == t2.val) { // 值相等: 判断是否包含
                result = this.containTree(t1, t2);
            }

            // 在左右子树中判断
            if (!result) {
                result = this.hasSubTree(t1.left, t2);
            }
            if (!result) {
                result = this.hasSubTree(t1.right, t2);
            }
        }

        return result;
    }

    // 树t1是否包含树t2
    private boolean containTree(TreeNode t1, TreeNode t2) {
        if (t2 == null) { // 树t2已经判断完
            return true;
        }
        if (t1 == null) {
            return false;
        }

        if (t1.val != t2.val) { // 比较值
            return false;
        }

        // 同时比较子树
        return this.containTree(t1.left, t2.left) &&
                this.containTree(t1.right, t2.right);
    }
}
