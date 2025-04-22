package com.spike.algorithm.adt;

import com.spike.algorithm.adt.Stack;
import org.junit.jupiter.api.Test;

public class StackTest {
    @Test
    public void create() {
        Stack<Integer> q = new Stack<>();

        q.push(1);
        q.push(2);
        q.push(3);
        q.push(4);
        q.push(5);

        int N = q.size();
        for (int i = 0; i < N; i++) {
            System.out.print(q.pop() + " ");
        }
    }
}
