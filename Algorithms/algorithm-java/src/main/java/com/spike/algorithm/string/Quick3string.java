package com.spike.algorithm.string;


/**
 * 三向字符串快速排序.
 */
public class Quick3string {
    private static int charAt(String s, int d) {
        if (d < s.length()) {
            return s.charAt(d);
        } else {
            return -1;
        }
    }

    public static void sort(String[] a) {
        sort(a, 0, a.length - 1, 0);
    }

    // 以第d个字符串将a[lo]到a[hi]排序
    private static void sort(String[] a, int lo, int hi, int d) {
        if (hi <= lo) {
            return;
        }

        int lt = lo; // lo -> hi
        int gt = hi; // hi <- lo
        int v = charAt(a[lo], d); // 以a[lo]的第d个字符划分
        int i = lo + 1;
        while (i <= gt) { // a[lo+1..hi]
            int t = charAt(a[i], d);
            if (t < v) {
                exch(a, lt++, i++); // 交换之后, i指向的"值"<=v, 步进
            } else if (t > v) {
                exch(a, i, gt--); // 交换之后, 仍需要比较i指向的"值"与v
            } else {
                i++; // 步进
            }
        }

        // a[lo..lt-1] < v=a[lt..gt] < a[gt+1..hi]
        sort(a, lo, lt - 1, d); // 部分1
        if (v >= 0) { // 部分2: 未到字符串末尾时, 按第d+1个字符继续排序
            sort(a, lt, gt, d + 1);
        }
        sort(a, gt + 1, hi, d); // 部分3

    }

    private static void exch(String[] a, int i, int j) {
        String temp = a[i];
        a[i] = a[j];
        a[j] = temp;
    }
}
