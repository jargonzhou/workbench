package com.spike.algorithm.adt;

import com.spike.algorithm.adt.ArrayStack;
import org.junit.jupiter.api.Test;

public class ArrayStackTest {
    @Test
    public void create() {
        ArrayStack<Integer> q = new ArrayStack<>();

        q.push(1);
        q.push(2);
        q.push(3);
        q.push(4);
        q.push(5);
        q.push(6);
        q.push(7);
        q.push(8);
        q.push(9);

        int N = q.size();
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < N; i++) {
            sb.append(q.pop() + " ");
        }
        System.out.println(sb.toString());
    }

}
