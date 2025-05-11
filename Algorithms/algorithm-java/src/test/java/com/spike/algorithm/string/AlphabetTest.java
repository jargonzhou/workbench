package com.spike.algorithm.string;

import org.junit.jupiter.api.Test;

public class AlphabetTest {
    @Test
    public void test() {
        final String alphabetString = "ABCDR";
        final String data = "ABRACADABRA!";

        Alphabet alphabet = new Alphabet(alphabetString);
        int R = alphabet.radix(); // 基数

        int[] count = new int[R];

        int N = data.length();
        for (int i = 0; i < N; i++) {
            if (alphabet.contains(data.charAt(i))) {
                count[alphabet.toIndex(data.charAt(i))]++;
            }
        }

        for (int c = 0; c < R; c++) {
            System.out.println(c + "/" + alphabet.toChar(c) + ": " + count[c]);
        }
    }
}
