package com.spike.algorithm.problems.array;

// 数组中重复的数字
public class O3 {
    public static void main(String[] args) {
        O3 o3 = new O3();

        // 长度为n, 数字都在0-n-1的范围内
        int[] array = new int[]{2, 3, 1, 0, 2, 5, 3};

        // 通常方法: 排序, 哈希表
        int result = o3.duplicate(array);
        // 2
        if (result != -1) {
            System.out.println(array[result]);
        }

        int[] array2 = new int[]{2, 3, 5, 4, 3, 2, 6, 7};
        result = o3.duplicate2(array2);
        // 3
        if (result != -1) {
            System.out.println(result);
        }
    }

    // 输出数组中任意一个重复的数字
    // 把值为m的放在下标m处
    // i: 下标
    // m: 值
    // -1: 没有重复
    // 不适用于返回第一个重复的数字: [6,3,2,0,2,5,0] - 返回0
    public int duplicate(int[] array) {
        if (array == null || array.length <= 1) {
            return -1;
        }

        int i = 0;
        while (i < array.length) {
            int m = array[i];
            if (i == m) {
                i++; // 已经将m放在下标m处: 步进
                continue;
            }

            int mm = array[m];
            if (m == mm) { // 找到重复的值
                return m;
            } else { // 交换下标i,m的值: 将值m放在下标m处
                array[i] = mm;
                array[m] = m;
            }
            // 不步进
        }

        return -1;
    }

    // 长度为n+1的数组, 数字在1-n的范围内, 返回任意一个重复的数字
    // 不能保证找到所有重复的数字: [2,3,5,4,3,2,6,7] - 在1-2中有1,2两个数字, 这个范围内2出现了2次
    public int duplicate2(int[] array) {
        if (array == null || array.length <= 1) {
            return -1;
        }

        // 数字范围: 初始1-n
        int start = 1;
        int end = array.length - 1;
        while (end >= start) {
            int mid = (end - start) / 2 + start;
            int count = this.count(array, start, mid); // [start, mid]

            if (end == start) { // 同一个数字
                if (count > 1) { // 找到重复的
                    return start; // 返回重复的数字
                } else {
                    break;
                }
            }

            // 是在左半部分, 还是在右半部分
            if (count > (mid - start + 1)) {
                end = mid; // [start, mid]
            } else {
                start = mid + 1; // [mid+1, end]
            }
        }

        return -1; // 未找到
    }

    // 数组中在[start, end]范围内的数字的数量
    private int count(int[] array, int start, int end) {
        if (array == null) {
            return 0;
        }
        int count = 0;
        for (int i = 0; i < array.length; i++) {
            if (start <= array[i] && array[i] <= end) {
                count++;
            }
        }
        return count;
    }
}
