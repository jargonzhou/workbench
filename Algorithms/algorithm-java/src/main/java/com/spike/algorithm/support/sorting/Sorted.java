package com.spike.algorithm.support.sorting;

/**
 * 已排序检查.
 *
 * @param <T>
 */
public class Sorted<T extends Comparable<T>> {
    private final T[] a;

    public Sorted(T[] a) {
        this.a = a;
    }

    public boolean sorted() {
        for (int i = 1; i <= a.length - 1; i++) {
            if (a[i - 1].compareTo(a[i]) > 0) {
                return false;
            }
        }
        return true;
    }
}
