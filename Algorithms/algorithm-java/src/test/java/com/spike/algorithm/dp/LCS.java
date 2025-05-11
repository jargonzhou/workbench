package com.spike.algorithm.dp;

// 最长公共子序列的长度
public class LCS {
    public static void main(String[] args) {
        char[] X = "abcde".toCharArray();
        char[] Y = "ace".toCharArray();
        int m = X.length;
        int n = Y.length;

        // dp[i][j]: X中前i个元素的子序列和Y中前j个元素的子序列的最长公共子序列的长度
        // dp[0][j], dp[i][0]: 子序列长度为0
        int[][] dp = new int[m + 1][n + 1];
        for (int i = 1; i <= m; i++) {
            for (int j = 1; j <= n; j++) {
                char xi = X[i - 1];
                char yj = Y[j - 1];
                if (xi == yj) { // 元素相同
                    dp[i][j] = dp[i - 1][j - 1] + 1;
                } else { // 元素不同
                    dp[i][j] = Math.max(dp[i - 1][j], dp[i][j - 1]);
                }
            }
        }

        System.out.println("Solution: " + dp[m][n]);
    }
}
