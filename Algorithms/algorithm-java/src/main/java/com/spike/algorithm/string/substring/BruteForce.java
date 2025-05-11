package com.spike.algorithm.string.substring;

/**
 * 暴力子字符串查找.
 */
public class BruteForce {

    /**
     * @param txt
     * @param pattern
     * @return 模式在文本中首次出现的位置. 不匹配时返回文本的长度.
     */
    public static int search(String txt, String pattern) {
        int N = txt.length();
        int M = pattern.length();

        if (N < M) {
            return N;
        }

        for (int i = 0; i <= N - M; i++) { // 文本索引
            int j;
            for (j = 0; j < M; j++) { // 模式索引
                if (txt.charAt(i + j) != pattern.charAt(j)) {
                    break;
                }
            }
            if (j == M) { // 找到匹配
                return i;
            }
        }

        // 未找到匹配
        return N;
    }

    // 显式回退
    public static int search2(String txt, String pattern) {
        int N = txt.length();
        int M = pattern.length();

        if (N < M) {
            return N;
        }

        int i, j;
        for (i = 0, j = 0; i < N && j < M; i++) {
            if (txt.charAt(i) == pattern.charAt(j)) {
                j++; // 步进模式索引
            } else { // 回退
                i -= j;
                j = 0;
            }
        }

        if (j == M) { // 找到匹配
            return i - M;
        } else {
            return N;
        }
    }

}
