package com.spike.algorithm.problems.string;

// 替换空格: %20
public class O5 {
    public static void main(String[] args) {
        O5 o5 = new O5();

        String s = "We are happy.";
        String result = o5.replaceBlank(s);
        // We%20are%20happy.
        System.out.println(result);
    }

    public String replaceBlank(String s) {
        char[] a = s.toCharArray();
        int blankCount = 0;
        for (int i = 0; i < a.length; i++) {
            if (a[i] == ' ') {
                blankCount++;
            }
        }

        char[] result = new char[a.length + 2 * blankCount]; // 每个空格多出来2个字符
        int j = 0;
        for (int i = 0; i < a.length; i++) {
            if (a[i] != ' ') {
                result[j++] = a[i];
            } else {
                result[j++] = '%';
                result[j++] = '2';
                result[j++] = '0';
            }
        }
        return new String(result);
    }
}
