package com.spike.algorithm.problems.tree;

// 二叉搜索树的后序遍历序列
public class O33 {
    public static void main(String[] args) {
        O33 o33 = new O33();

        int[] a = new int[]{5, 7, 6, 9, 11, 10, 8};
        boolean result = o33.verify(a);
        System.out.println(result); // true
        int[] a2 = new int[]{7, 4, 6, 5};

        result = o33.verify(a2);
        System.out.println(result); // false
    }

    public boolean verify(int[] a) {
        if (a == null || a.length == 0) {
            return false;
        }
        if (a.length == 1) {
            return true;
        }
        return this.verify(a, 0, a.length - 1);
    }

    private boolean verify(int[] a, int lo, int hi) {
        if (lo >= hi) {
            return true;
        }

        int root = a[hi];
        int rightIndex = hi;
        for (int i = lo; i <= hi - 1; i++) { // 找到右子树开始处
            if (a[i] > root) {
                rightIndex = i;
                break;
            }
        }
        for (int i = rightIndex; i <= hi - 1; i++) {
            if (a[i] < root) {
                return false;
            }
        }

        // 递归验证
        return this.verify(a, lo, rightIndex - 1) &&
                this.verify(a, rightIndex, hi - 1);
    }
}
