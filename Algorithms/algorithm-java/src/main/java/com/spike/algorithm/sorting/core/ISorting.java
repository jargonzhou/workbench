package com.spike.algorithm.sorting.core;

/**
 * 排序接口.
 */
public interface ISorting<T extends Comparable<T>> {
    /**
     * 执行数组排序操作.
     */
    void sort(T[] a);
}
