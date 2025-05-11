package com.spike.algorithm.dp;

// 0/1背包问题
public class Pack01 {

    public static void main(String[] args) {
        int N = 4; // 物品数量
        int C = 9; // 背包容量
        int[] c = new int[]{2, 3, 6, 5}; // 体积
        int[] w = new int[]{6, 3, 5, 4}; // 价值

        // dp[i][j]: 将前i个物品装入容量j的背包中获取的最大价值
        // dp[0][j]: 不装物品时最大价值为0, 容量为0时最大价值为0
        int[][] dp = new int[N + 1][C + 1];

        for (int i = 1; i <= N; i++) {
            for (int j = 0; j <= C; j++) {
                int ci = c[i - 1];
                int wi = w[i - 1];

                if (ci > j) { // 无法装入物品i
                    System.out.printf("[%d][%d]: -%d\n", i, j, i - 1);
                    dp[i][j] = dp[i - 1][j];
                } else {
                    int cond21 = dp[i - 1][j];// i不装入
                    int cond22 = dp[i - 1][j - ci] + wi; // i 装入
                    if (cond22 > cond21) {
                        System.out.printf("[%d][%d]: +%d\n", i, j, i - 1);
                        dp[i][j] = cond22;
                    } else {
                        System.out.printf("[%d][%d]: -%d\n", i, j, i - 1);
                        dp[i][j] = cond21;
                    }
                }
            }
        }

        System.out.println("Solution: " + dp[N][C]);
    }
}
