package com.spike.algorithm.string;

import com.google.common.collect.Lists;
import com.spike.algorithm.support.sorting.Sorted;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.List;

public class LSDTest {
    @Test
    public void sort() {
        List<String> list = Lists.newArrayList(
                "4PGC938",
                "2IYE230",
                "3CIO720",
                "1ICK750",
                "1OHV845",
                "4JZY524",
                "1ICK750",
                "3CIO720",
                "1OHV845",
                "1OHV845",
                "2RLA629",
                "2RLA629",
                "3ATW723");
        String[] a = list.toArray(new String[0]);
        LSD.sort(a, list.get(0).length());
        for (int i = 0; i < a.length; i++) {
            System.out.println(a[i]);
        }
        Assertions.assertThat(new Sorted<>(a).sorted()).isTrue();
    }
}
