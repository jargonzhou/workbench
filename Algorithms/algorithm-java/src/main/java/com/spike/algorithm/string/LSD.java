package com.spike.algorithm.string;

/**
 * 低位优先的字符串排序.
 *
 * @see KeyIndexedCounting
 */
public class LSD {
    /**
     * @param a 待排序字符串数组
     * @param W 字符串长度
     */
    public static void sort(String[] a, int W) {
        int N = a.length;
        int R = 256;
        String[] aux = new String[N];

        for (int d = W - 1; d >= 0; d--) {
            // 根据第d个字符, 用键索引计数法排序
            int[] count = new int[R + 1];
            // 频率统计
            for (int i = 0; i < N; i++) {
                count[a[i].charAt(d) + 1]++;
            }
            // 将频率转换成起始索引
            for (int r = 0; r < R; r++) {
                count[r + 1] += count[r];
            }
            // 数据分类
            for (int i = 0; i < N; i++) {
                aux[count[a[i].charAt(d)]++] = a[i];
            }
            // 回写
            for (int i = 0; i < N; i++) {
                a[i] = aux[i];
            }
        }
    }
}
