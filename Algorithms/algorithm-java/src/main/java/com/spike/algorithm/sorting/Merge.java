package com.spike.algorithm.sorting;

import com.spike.algorithm.sorting.core.ISorting;
import com.spike.algorithm.sorting.core.MergingOp;
import com.spike.algorithm.sorting.core.SortingData;

/**
 * 归并排序: 自顶向下.
 * <p>
 * 递归方式处理, 归并左右两部分的排序结果, 使得数组元素有序.
 */
public class Merge<T extends Comparable<T>> extends MergingOp<T> implements ISorting<T> {

    @Override
    public void sort(T[] a) {
        this.sort(a, 0, a.length - 1);
    }

    private void sort(T[] a, int lo, int hi) {
        if (hi <= lo) return;

        // 左右两部分分别排序
        int mid = lo + (hi - lo) / 2;
        this.sort(a, lo, mid);
        this.sort(a, mid + 1, hi);

        // 归并: 使得有序
        super.merge(a, lo, mid, hi); // 使用辅助数组

        super.show(a);// DEBUG
    }

    public static void main(String[] args) {
        Character[] a = SortingData.data();
        Merge<Character> sorting = new Merge<>();
        sorting.sort(a);
        System.out.println(sorting.isSorted(a));
        sorting.show(a);
    }
}