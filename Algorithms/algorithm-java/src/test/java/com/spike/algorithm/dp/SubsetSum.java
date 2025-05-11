package com.spike.algorithm.dp;

// 子集和
public class SubsetSum {
    public static void main(String[] args) {
        int[] S = new int[]{6, 2, 9, 8, 3, 7};
        int n = S.length;
        int M = 5;
//        int M = 4;

        // dp[i][j]: S的前i个元素存在一个子集和等于j
        boolean[][] dp = new boolean[n + 1][M + 1];
        dp[0][0] = true; // 空集和为0

        for (int i = 1; i <= n; i++) {
            for (int j = 0; j <= M; j++) {
                int si = S[i - 1];
                if (si > j) { // 不能在子集中
                    dp[i][j] = dp[i - 1][j];
                } else { // 可以在子集中: 放/不放
                    dp[i][j] = dp[i - 1][j] || dp[i - 1][j - si];
                }
            }
        }

        System.out.println("Solution: " + dp[n][M]);
    }

}
