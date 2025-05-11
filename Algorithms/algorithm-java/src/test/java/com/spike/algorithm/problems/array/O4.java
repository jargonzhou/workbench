package com.spike.algorithm.problems.array;

// 二维数组中的查找
public class O4 {
    public static void main(String[] args) {
        O4 o4 = new O4();
        int[][] matrix = new int[][]{
                {1, 2, 8, 9},
                {2, 4, 9, 12},
                {4, 7, 10, 13},
                {6, 8, 11, 15}
        };
        boolean result = o4.find(matrix, 7);
        // true
        System.out.println(result);

        result = o4.find(matrix, 5);
        // false
        System.out.println(result);
    }

    public boolean find(int[][] matrix, int target) {
        if (matrix == null) {
            return false;
        }
        int col = matrix.length;
        if (col == 0) {
            return false;
        }
        int row = matrix[0].length;
        if (row == 0) {
            return false;
        }

        // 选取左下角的元素: 或者右上角的元素
        int r = row - 1; // 行
        int c = 0; // 列
        int v;
        for (; r >= 0 && r < row && c >= 0 && c < col; ) {
            v = matrix[r][c];
            if (v == target) {
                return true;
            } else if (v < target) {
                c++;
            } else {
                r--;
            }
        }
        return false;
    }
}
