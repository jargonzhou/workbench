package com.spike.algorithm.dp;

// 自顶向下斐波那契: 记忆化
public class TopDownFib {
    private int[] memoize;

    public TopDownFib(int N) {
        this.memoize = new int[N];
    }

    public int fib(int n) {
        if (n == 1 || n == 2) {
            return 1;
        }
        if (memoize[n] != 0) {
            return memoize[n];
        }
        memoize[n] = fib(n - 1) + fib(n - 2);
        return memoize[n];
    }

    public static void main(String[] args) {
        System.out.println(new TopDownFib(255).fib(42));
    }
}
