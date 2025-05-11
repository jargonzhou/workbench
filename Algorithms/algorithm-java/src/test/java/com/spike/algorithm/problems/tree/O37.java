package com.spike.algorithm.problems.tree;

// 序列化和反序列化二叉树
public class O37 {
    public static void main(String[] args) {
        O37 o37 = new O37();

        TreeNode root = new TreeNode(1,
                new TreeNode(2,
                        new TreeNode(4),
                        null),
                new TreeNode(3,
                        new TreeNode(5),
                        new TreeNode(6)));
        // 1 2 3 4 5 6
        TreeNode.level(root);
        System.out.println();

        String ser = o37.serialize(root);
        // 1,2,4,$,$,$,3,5,$,$,6,$,$,
        System.out.println(ser);

        TreeNode result = o37.deserialize(ser);
        // 1 2 3 4 5 6
        TreeNode.level(result);
        System.out.println();
    }

    private int index = -1;

    // 空节点: $
    // 节点之间分隔: ,
    public String serialize(TreeNode x) {
        StringBuilder sb = new StringBuilder();
        if (x == null) {
            sb.append("$,");
            return sb.toString();
        }
        // 先序遍历
        sb.append(x.val + ",");
        sb.append(this.serialize(x.left));
        sb.append(this.serialize(x.right));
        return sb.toString();
    }

    public TreeNode deserialize(String input) {
        String[] nodes = input.split(",");
        return this.doSerialize(nodes);
    }

    private TreeNode doSerialize(String[] nodes) {
        index++;

        TreeNode x = null;
        if (!nodes[index].equals("$")) {
            // 先序遍历
            x = new TreeNode(Integer.parseInt(nodes[index]));
            x.left = this.doSerialize(nodes);
            x.right = this.doSerialize(nodes);
        }
        return x;
    }
}
