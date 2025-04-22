package com.spike.algorithm.searching;

import com.spike.algorithm.searching.BST;
import com.spike.algorithm.searching.SequentialSearchST;
import com.spike.algorithm.searching.core.ST;
import com.spike.algorithm.support.io.In;
import com.spike.algorithm.support.io.StdOut;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.Test;

import java.io.File;

public class FrequencyCounter {

    @Test
    public void SequentialSearchST() {
        doTest(new SequentialSearchST<>());
    }

    @Test
    public void BST() {
        doTest(new BST<>());
    }

    private void doTest(ST<String, Integer> st) {
        final int minlen = 1;
        In in = new In(new File("src/test/resources/algs4-data/tinyTale.txt"));
        String[] words = in.readAllStrings();
        for (String word : words) {
            if (word.length() < minlen) {
                continue;
            }
            if (st.contains(word)) {
                st.put(word, st.get(word) + 1);
            } else {
                st.put(word, 1);
            }
        }

        for (String word : st.keys()) {
            StdOut.println(word + ": " + st.get(word));
        }

        String max = " ";
        st.put(max, 0);
        for (String word : st.keys()) {
            if (st.get(word) > st.get(max)) {
                max = word;
            }
        }
        Assertions.assertThat(max).isEqualTo("it");
        Assertions.assertThat(st.get(max)).isEqualTo(10);
        StdOut.println("max=" + max + " " + st.get(max));
    }

}
