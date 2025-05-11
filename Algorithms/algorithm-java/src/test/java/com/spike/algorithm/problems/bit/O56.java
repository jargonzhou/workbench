package com.spike.algorithm.problems.bit;

// 1: 数组中只出现一次的数字: 除两个数字之外, 其他均出现两次
// 2: 数组中唯一只出现一次的数字: 除一个数字只出现一次之外, 其他数字均出现了三次
public class O56 {
    public static void main(String[] args) {
        O56 o56 = new O56();
        int[] a = new int[]{2, 4, 3, 6, 3, 2, 5, 5};
        int[] result = o56.problem1(a);
        // 6 4
        if (result != null) {
            System.out.println(result[0] + " " + result[1]);
        }

        int[] a2 = new int[]{1, 2, 2, 2, 3, 3, 3};
        int result2 = o56.problem2(a2);
        // 1
        System.out.println(result2);
    }

    public int[] problem1(int[] a) {
        if (a == null || a.length < 4) {
            return null;
        }

        // 异或
        int xor = 0;
        for (int i = 0; i < a.length; i++) {
            xor ^= a[i];
        }
        int temp = xor & (-xor); // 去掉右边起第一个1的左边: 结果例10000
        int n1 = 0;
        int n2 = 0;
        for (int i = 0; i < a.length; i++) {
            if ((a[i] & temp) != 0) { // 不为0说明一个数中位为1, 另一个数中位为0
                n1 ^= a[i];
            } else {
                n2 ^= a[i];
            }
        }
        int[] result = new int[2];
        result[0] = n1;
        result[1] = n2;
        return result;
    }

    public int problem2(int[] a) {
        if (a == null || a.length < 4) {
            return -1;
        }
        int[] bitSum = new int[Integer.SIZE];
        for (int i = 0; i < a.length; i++) {
            // 逐位求1的和
            int mask = 1;
            for (int j = Integer.SIZE - 1; j >= 0; j--) {
                int bit = a[i] & mask;
                if (bit != 0) { // 位为1: 求和/计数
                    bitSum[j] += 1;
                }
                mask <<= 1;
            }
        }

        // 各位中和为3的倍数, 对应位为0, 否则为1
        int result = 0;
        for (int i = 0; i < Integer.SIZE; i++) {
            result <<= 1;
            result += bitSum[i] % 3;
        }
        return result;
    }

}
