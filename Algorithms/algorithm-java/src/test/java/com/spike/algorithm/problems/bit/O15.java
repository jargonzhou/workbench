package com.spike.algorithm.problems.bit;

// 二进制中1个个数
public class O15 {
    public static void main(String[] args) {
        O15 o15 = new O15();

        // 111
        System.out.println(Integer.toBinaryString(7));
        // 11111111111111111111111111111001 - 补码表示
        System.out.println(Integer.toBinaryString(-7));

        // 3
        System.out.println(o15.count(7));
        // 30
        System.out.println(o15.count(-7));

        // 3
        System.out.println(o15.count2(7));
        // 30
        System.out.println(o15.count2(-7));
    }

    public int count(int n) {
        int result = 0;
        int flag = 1;
        // 通过左移动1, 逐位判断是否是1
        while (flag != 0) {
            if ((n & flag) != 0) { // 是1
                result++;
            }

            flag <<= 1;
        }
        return result;
    }

    public int count2(int n) {
        // 将整数-1, 再和原整数与运算: 将整数的最右边的1变为0
        int result = 0;
        while (n != 0) {
            result++;

            n = n & (n - 1);
        }
        return result;
    }
}
