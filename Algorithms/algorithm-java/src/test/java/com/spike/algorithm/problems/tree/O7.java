package com.spike.algorithm.problems.tree;

// 重建二叉树
public class O7 {
    public static void main(String[] args) {
        O7 o7 = new O7();

        int[] pre = new int[]{1, 2, 4, 7, 3, 5, 6, 8}; // 先序
        int[] in = new int[]{4, 7, 2, 1, 5, 3, 8, 6}; // 中序

        TreeNode x = o7.construct(pre, 0, pre.length - 1,
                in, 0, in.length - 1);

        // 1 2 4 7 3 5 6 8
        TreeNode.pre(x);
        System.out.println();

        // 4 7 2 1 5 3 8 6
        TreeNode.in(x);
        System.out.println();
    }


    public TreeNode construct(int[] pre, int startPre, int endPre,
                              int[] in, int startIn, int endIn) {
        if (pre == null || in == null) {
            return null;
        }
        if (startPre > endPre || startIn > endIn) {
            return null;
        }

        // 根节点
        TreeNode root = new TreeNode(pre[startPre]);
        // 沿着中序遍历结果, 找到根
        for (int i = startIn; i <= endIn; i++) {
            if (in[i] == pre[startPre]) {
                // 左子树
                root.left = this.construct(pre, startPre + 1, startPre + (i - startIn),
                        in, startIn, i - 1);
                // 右子树
                root.right = this.construct(pre, startPre + (i - startIn) + 1, endPre,
                        in, i + 1, endIn);
            }
        }
        return root;
    }
}
