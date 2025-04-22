package com.spike.algorithm.sorting.core;

/**
 * 归并数组操作.
 */
public class MergingOp<T extends Comparable<T>> extends Op<T> {

    /**
     * 辅助数组.
     */
    protected T[] aux;

    /**
     * 将a[lo..mid]与a[mid+1..hi]合并.
     *
     * @param a
     * @param lo
     * @param mid
     * @param hi
     */
    @SuppressWarnings("unchecked")
    public void merge(T[] a, int lo, int mid, int hi) {
        // 两个数组索引
        int i = lo; // [lo, mid]
        int j = mid + 1; // [mid+1, hi]

        // 构造辅助数组aux
        if (aux == null) {
            aux = (T[]) new Comparable[a.length];
        }
        for (int k = lo; k <= hi; k++) {
            aux[k] = a[k];
        }

        // 归并到数组a中
        for (int k = lo; k <= hi; k++) {
            // 左边已结束
            if (i > mid) {
                a[k] = aux[j++];
            }
            // 右边已结束
            else if (j > hi) {
                a[k] = aux[i++];
            }
            // 右边的值小
            else if (this.less(aux[j], aux[i])) { // 比较操作
                a[k] = aux[j++];
            }
            // 左边的值小
            else {
                a[k] = aux[i++];
            }
        }
    }
}
