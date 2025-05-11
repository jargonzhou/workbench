package com.spike.algorithm.string.substring;

public class KMP {
    private final String pattern;
    // 维度: R x M
    // 模式中每个字符表示一个状态, 结束状态为M
    // 含义: dfa[c][j] 处于模式j处遇到c的下一个模式字符位置
    private int[][] dfa;

    public KMP(String pattern) {
        this.pattern = pattern;

        // 由模式字符串构造DFA
        int M = pattern.length();
        int R = 256;
        dfa = new int[R][M]; // 下一状态均为初始状态0

        dfa[pattern.charAt(0)][0] = 1; // 初始化状态0遇到模式首字符: 下一状态1

        // 依次处理状态

        int X = 0; // X: 重启位置
        for (int j = 1; j < M; j++) {
            // 计算dfa[][j]
            for (int c = 0; c < R; c++) {
                dfa[c][j] = dfa[c][X]; // 匹配失败: 使用重启位置
            }
            dfa[pattern.charAt(j)][j] = j + 1; // 匹配成功: 结束状态为M

            X = dfa[pattern.charAt(j)][X]; // 维护重启位置
        }
    }

    public int search(String txt) {
        int N = txt.length();
        int M = pattern.length();
        int i, j;
        for (i = 0, j = 0; i < N && j < M; i++) {
            j = dfa[txt.charAt(i)][j]; // 回退模式索引j
        }
        if (j == M) { // 找到匹配
            return i - M;
        } else {
            return N;
        }
    }

}
