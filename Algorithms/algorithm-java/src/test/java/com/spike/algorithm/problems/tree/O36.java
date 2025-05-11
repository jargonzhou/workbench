package com.spike.algorithm.problems.tree;

// 二叉搜索树与双向链表
public class O36 {
    private TreeNode head;
    private TreeNode tail;

    public static void main(String[] args) {
        O36 o36 = new O36();

        TreeNode root = new TreeNode(10,
                new TreeNode(6,
                        new TreeNode(4),
                        new TreeNode(8)),
                new TreeNode(14,
                        new TreeNode(12),
                        new TreeNode(16)));

        TreeNode h = o36.convert(root);

        // 4 6 8 10 12 14 16
        TreeNode n = h;
        while (n != null) {
            System.out.print(n.val + " ");
            n = n.right;
        }
        System.out.println();
    }

    public TreeNode convert(TreeNode root) {
        this.doConvert(root);
        return head;
    }

    private void doConvert(TreeNode x) {
        if (x == null) {
            return;
        }

        // 中序遍历
        this.doConvert(x.left);
        if (tail == null) {
            head = x; // head唯一一次赋值
            tail = x;
        } else {
            // 双向链接: tail
            tail.right = x;
            x.left = tail;
            // 步进
            tail = x;
        }
        this.doConvert(x.right);

    }


}
