package com.spike.algorithm.string;

/**
 * 高位优先的字符串排序.
 *
 * @see KeyIndexedCounting
 */
public class MSD {
    private static int R = 256; // 基数
    private static final int M = 15; // 小数组的大小阈值
    private static String[] aux;

    private static int charAt(String s, int d) {
        if (d < s.length()) {
            return s.charAt(d);
        } else {
            return -1; // 超过字符串末尾
        }
    }

    public static void sort(String[] a) {
        int N = a.length;
        aux = new String[N];
        sort(a, 0, N - 1, 0);
    }

    // 以第d个字符串将a[lo]到a[hi]排序
    private static void sort(String[] a, int lo, int hi, int d) {
        if (hi < lo + M) {
            insertionSort(a, lo, hi, d);
            return;
        }

        int[] count = new int[R + 2];
        // 频率统计
        for (int i = lo; i <= hi; i++) {
            count[charAt(a[i], d) + 2]++; // +2: +1, 额外的位置
        }
        // 将频率转换成起始索引
        for (int r = 0; r < R + 1; r++) {
            count[r + 1] += count[r];
        }
        // 数据分类
        for (int i = lo; i <= hi; i++) {
            aux[count[charAt(a[i], d) + 1]++] = a[i]; // +1: 表示超过字符串末尾, 用0表示字符串末尾
        }
        // 回写
        for (int i = lo; i <= hi; i++) {
            a[i] = aux[i - lo];
        }

        // 递归的以每个字符为键进行排序
        for (int r = 0; r < R; r++) {
            sort(a, lo + count[r], lo + count[r + 1] - 1, d + 1); // d+1
        }

    }

    private static void insertionSort(String[] a, int lo, int hi, int d) {
        int N = a.length;
        for (int i = lo; i <= hi; i++) {
            // 将第i个元素放到左边部分已部分排序中的恰当位置: 通过依次左移一个元素
            for (int j = i; j > lo && less(a[j], a[j - 1], d); j--) {
                exch(a, j, j - 1);
            }
        }
    }


    private static boolean less(String v, String w, int d) {
        // PRE: v.substring(0,d) 与 w.substring(0,d)相同
        for (int i = d; i < Math.min(v.length(), w.length()); i++) {
            if (v.charAt(i) < w.charAt(i)) {
                return true;
            }
            if (v.charAt(i) > w.charAt(i)) {
                return false;
            }
        }
        // 较短的字符串排在前面
        return v.length() < w.length();
    }


    private static void exch(String[] a, int i, int j) {
        String temp = a[i];
        a[i] = a[j];
        a[j] = temp;
    }
}
