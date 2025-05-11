package com.spike.algorithm.string;

import java.util.Objects;

/**
 * 键索引计数.
 */
public class KeyIndexedCounting {

    public static class InputItem implements Comparable<InputItem> {
        private final String name;
        private final int group;

        public InputItem(String name, int group) {
            this.name = name;
            this.group = group;
        }

        public String name() {
            return name;
        }

        public int key() {
            return group;
        }

        @Override
        public int compareTo(InputItem o) {
            if (group < o.group) {
                return -1;
            } else if (group == o.group) {
                return 0;
            } else {
                return 1;
            }
        }
    }

    public static void sort(InputItem[] a, int groupCount) {
        if (Objects.isNull(a) || a.length == 0) {
            return;
        }

        int R = groupCount + 1; // 带上第0组
        int N = a.length;

        InputItem[] aux = new InputItem[N];
        int[] count = new int[R + 1]; // +1: 需要一个额外的位置

        // 频率统计
        for (int i = 0; i < N; i++) {
            count[a[i].key() + 1]++; // +1
        }
        // 将频率转换为起始索引
        for (int r = 0; r < R; r++) {
            count[r + 1] += count[r]; // +=
        }
        // 数据分类
        for (int i = 0; i < N; i++) {
            aux[count[a[i].key()]++] = a[i]; // count[x]++
        }
        // 回写
        for (int i = 0; i < N; i++) {
            a[i] = aux[i];
        }
    }
}
