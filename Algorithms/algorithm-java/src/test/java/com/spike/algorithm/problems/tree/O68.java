package com.spike.algorithm.problems.tree;

// 树中两个节点的最低公共组件
public class O68 {

    public static void main(String[] args) {
        O68 o68 = new O68();

        TreeNode t1 = new TreeNode(1,
                new TreeNode(0),
                new TreeNode(4,
                        new TreeNode(3),
                        new TreeNode(5)));
        TreeNode t12 = new TreeNode(12,
                new TreeNode(11),
                new TreeNode(14));
        TreeNode bst = new TreeNode(7,
                t1,
                t12);
        TreeNode bstCommon = o68.bstCommon(bst, t1, t12);
        // 7
        System.out.println(bstCommon.val);

        TreeNode tF = new TreeNode('F');
        TreeNode tH = new TreeNode('H');
        TreeNode tree = new TreeNode('A',
                new TreeNode('B',
                        new TreeNode('D',
                                tF,
                                new TreeNode('G')),
                        new TreeNode('E',
                                tH,
                                new TreeNode('I'))),
                new TreeNode('C'));
        TreeNode treeCommon = o68.common(tree, tF, tH);
        // B
        System.out.println((char) treeCommon.val);
    }

    // 二叉搜索树
    // 一个节点也可以是它自己的祖先
    public TreeNode bstCommon(TreeNode t, TreeNode x, TreeNode y) {
        if (t == null || x == null || y == null) { // 空树
            return null;
        }

        if (t == x || t == y) { // 有一个是根节点
            return t;
        }

        if (x.val < t.val && y.val < t.val) { // 左子树
            return this.bstCommon(t.left, x, y);
        } else if (x.val > t.val && y.val > t.val) { // 右子树
            return this.bstCommon(t.right, x, y);
        } else {
            return t; // 为根节点
        }
    }

    // 普通树
    public TreeNode common(TreeNode t, TreeNode x, TreeNode y) {
        if (t == null || x == null || y == null) {
            return null;
        }
        if (t == x || t == y) {
            return t;
        }
        // 分别在左右两边找
        TreeNode left = this.common(t.left, x, y);
        TreeNode right = this.common(t.right, x, y);
        if (left == null) { // 左子树没找到: 在右子树中
            return right;
        } else if (right == null) { // 右子树没找到: 在左子树中
            return left;
        } else { // 左右子树均没找到: 根节点
            return t;
        }
    }
}
