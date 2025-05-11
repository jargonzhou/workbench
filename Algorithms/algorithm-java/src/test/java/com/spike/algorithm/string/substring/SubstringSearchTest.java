package com.spike.algorithm.string.substring;

import org.junit.jupiter.api.Test;

public class SubstringSearchTest {
    // private static final String txt = "INAHAYSTACKNEEDLEINA";
    private static final String txt = "AABRAACADABRAACAADABRA";
    private static final int N = txt.length();
    // private static final String pattern = "NEEDLE";
    private static final String pattern = "AACAA";
    private static final int M = pattern.length();

    @Test
    public void bruteForce() {
        int result = BruteForce.search(txt, pattern);
        output(result);
    }

    private void output(int result) {
        if (result != N) {
            System.out.println("Found: " + txt.substring(0, result)
                    + "[" + txt.substring(result, result + M) + "]"
                    + txt.substring(result + M));
        } else {
            System.out.println("Not found");
        }
    }

    @Test
    public void KMP() {
        KMP kmp = new KMP(pattern);
        int result = kmp.search(txt);
        output(result);
    }
}
