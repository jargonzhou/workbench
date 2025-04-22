package com.spike.algorithm.support;

import com.spike.algorithm.example.ThreeSum;
import com.spike.algorithm.support.Stopwatch;
import com.spike.algorithm.support.io.StdRandom;
import org.junit.jupiter.api.Test;

public class StopWatchTest {
    @Test
    public void stopWatch() {
        // for (int N = 250; N < Integer.MAX_VALUE; N += N) {
        for (int N = 250; N <= 2000; N += N) {
            experiment(N);
        }
    }

    // 问题规模为N的实验
    void experiment(int N) {
        int MAX = 1000000;
        int[] a = new int[N];
        for (int i = 0; i < N; i++) {
            a[i] = StdRandom.uniform(-MAX, MAX);
        }

        Stopwatch sw = new Stopwatch();
        int cnt = ThreeSum.basicSolution(a); // 三数和为0
        System.out.printf("N=%7d, Time=%5.1f, found: %d\n", N, sw.elapsedTime(), cnt);
    }
}
