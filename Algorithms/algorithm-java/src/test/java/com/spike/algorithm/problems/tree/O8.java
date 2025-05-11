package com.spike.algorithm.problems.tree;

// 二叉树中序遍历的下一个节点
public class O8 {
    public static void main(String[] args) {
        O8 o8 = new O8();

        TreeNode a = new TreeNode('a');
        TreeNode b = new TreeNode('b');
        TreeNode d = new TreeNode('d');
        TreeNode e = new TreeNode('e');
        TreeNode h = new TreeNode('h');
        TreeNode i = new TreeNode('i');
        TreeNode c = new TreeNode('c');
        TreeNode f = new TreeNode('f');
        TreeNode g = new TreeNode('g');

        a.left = b; b.parent = a;
        a.right = c; c.parent = a;
        b.left = d; d.parent = b;
        b.right = e; e.parent = b;
        e.left = h; h.parent = e;
        e.right = i; i.parent =e;
        c.left = f; f.parent =c;
        c.right = g;g.parent = c;

        System.out.println(o8.next(d) == b);
        System.out.println(o8.next(b) == h);
        System.out.println(o8.next(h) == e);
        System.out.println(o8.next(e) == i);
        System.out.println(o8.next(i) == a);
        System.out.println(o8.next(a) == f);
        System.out.println(o8.next(f) == c);
        System.out.println(o8.next(c) == g);
        System.out.println(o8.next(g) == null);
    }

    public TreeNode next(TreeNode x) {
        // 右节点不为空: 右子树的最左子孙节点
        if (x.right != null) {
            TreeNode r = x.right;
            while (r.left != null) {
                r = r.left;
            }
            return r;
        }

        // 右节点为空, 是父节点的左节点: 父节点
        if (x.parent != null && x.parent.left == x) {
            return x.parent;
        }

        // 右节点为空, 是父节点的右节点: 往上走, 直到遇到是其父节点的左节点的节点, 返回该节点的父节点
        if (x.parent != null) {
            TreeNode p = x.parent;
            while (p.parent != null && p.parent.right == p) {
                p = p.parent;
            }
            return p.parent;
        }

        return null;
    }
}
