package com.spike.algorithm.searching;

import com.google.common.base.Strings;
import com.spike.algorithm.searching.RedBlackBST;
import org.junit.jupiter.api.Test;

public class RedBlackBSTTest {
    @Test
    public void test() {
        RedBlackBST<String, Integer> rb = new RedBlackBST<>();
        int i = 0;
        for (String key : "S E A R C H E X A M P L E".split("\\s")) {
            rb.put(key, i);
            i++;
        }
        rb.dump();

        System.out.println();
        rb.delete("E");
        rb.delete("M");
        rb.dump();
    }
}
