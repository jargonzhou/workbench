package com.spike.algorithm.string;

import com.google.common.collect.Lists;
import com.spike.algorithm.support.sorting.Sorted;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.List;

public class MSDTest {
    @Test
    public void sort() {
        List<String> list = Lists.newArrayList(
                "she",
                "sells",
                "seashells",
                "by",
                "the",
                "seashore",
                "the",
                "shells",
                "she",
                "sells",
                "are",
                "surely",
                "seashells");
        String[] a = list.toArray(new String[0]);
        MSD.sort(a);
        for (int i = 0; i < a.length; i++) {
            System.out.println(a[i]);
        }
        Assertions.assertThat(new Sorted<>(a).sorted()).isTrue();
    }
}
