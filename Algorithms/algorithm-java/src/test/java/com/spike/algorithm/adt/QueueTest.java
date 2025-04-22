package com.spike.algorithm.adt;

import com.spike.algorithm.adt.Queue;
import org.junit.jupiter.api.Test;

public class QueueTest {
    @Test
    public void queue() {
        Queue<Integer> q = new Queue<>();

        q.enqueue(1);
        q.enqueue(2);
        q.enqueue(3);
        q.enqueue(4);
        q.enqueue(5);

        int N = q.size();
        for (int i = 0; i < N; i++) {
            System.out.print(q.dequeue() + " ");
        }
    }
}
