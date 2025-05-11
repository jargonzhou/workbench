package com.spike.algorithm.dp;

// 自底向上斐波那契: 制表递推
public class BottomUpFib {
    private int[] dp;

    public BottomUpFib(int N) {
        this.dp = new int[N];
    }

    public int fib(int n) {
        dp[1] = 1;
        dp[2] = 1;

        for (int i = 3; i <= n; i++) {
            dp[i] = dp[i - 1] + dp[i - 2];
        }

        return dp[n];
    }

    public static void main(String[] args) {
        System.out.println(new BottomUpFib(255).fib(42));
    }
}
