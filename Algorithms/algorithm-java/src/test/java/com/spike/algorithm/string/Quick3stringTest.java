package com.spike.algorithm.string;

import com.google.common.collect.Lists;
import com.spike.algorithm.support.sorting.Sorted;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.List;

public class Quick3stringTest {

    @Test
    public void sort() {
        List<String> list = Lists.newArrayList(
                "edu.princeton.cs",
                "com.apple",
                "edu.princeton.cs",
                "com.cnn",
                "com.google",
                "edu.uva.cs",
                "edu.princeton.cs",
                "edu.princeton.cs.www",
                "edu.uva.cs",
                "edu.uva.cs",
                "edu.uva.cs",
                "com.adobe",
                "edu.princeton.ee");

        String[] a = list.toArray(new String[0]);
        Quick3string.sort(a);
        for (String s : a) {
            System.out.println(s);
        }
        Assertions.assertThat(new Sorted<>(a).sorted()).isTrue();
    }
}
