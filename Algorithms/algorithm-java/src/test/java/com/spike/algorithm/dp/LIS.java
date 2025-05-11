package com.spike.algorithm.dp;

// 最长的单调递增子序列的长度
public class LIS {
    public static void main(String[] args) {
        int[] A = new int[]{5, 6, 7, 4, 2, 8, 3}; // 5,6,7,8
        int n = A.length;

        // dp[i]: 以第i个数为结尾的最长递增子序列的长度
        int[] dp = new int[n];
        dp[0] = 1; // 只有1个数: 长度为1
        for (int i = 1; i < n; i++) {
            int max = 0;
            for (int j = 0; j < i; j++) { // 所有能构成递增的
                if (A[j] < A[i]) {
                    max = Math.max(max, dp[j] + 1);
                }
            }
            dp[i] = max;
        }

        int max = dp[0];
        for (int i = 1; i < n; i++) {
            max = Math.max(max, dp[i]);
        }
        System.out.println("Solution: " + max);
    }
}
