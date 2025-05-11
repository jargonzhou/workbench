package com.spike.algorithm.string;

import com.google.common.collect.Lists;
import com.spike.algorithm.support.sorting.Sorted;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.List;

public class KeyIndexedCountingTest {
    @Test
    public void sort() {
        List<KeyIndexedCounting.InputItem> list = Lists.newArrayList(
                new KeyIndexedCounting.InputItem("Anderson", 2),
                new KeyIndexedCounting.InputItem("Brown", 3),
                new KeyIndexedCounting.InputItem("Davis", 3),
                new KeyIndexedCounting.InputItem("Garcia", 4),
                new KeyIndexedCounting.InputItem("Harris", 1),
                new KeyIndexedCounting.InputItem("Jackson", 3),
                new KeyIndexedCounting.InputItem("Johnson", 4),
                new KeyIndexedCounting.InputItem("Jones", 3),
                new KeyIndexedCounting.InputItem("Martin", 1),
                new KeyIndexedCounting.InputItem("Martinez", 2),
                new KeyIndexedCounting.InputItem("Miller", 2),
                new KeyIndexedCounting.InputItem("Moore", 1),
                new KeyIndexedCounting.InputItem("Robinson", 2),
                new KeyIndexedCounting.InputItem("Smith", 4),
                new KeyIndexedCounting.InputItem("Taylor", 3),
                new KeyIndexedCounting.InputItem("Thomas", 4),
                new KeyIndexedCounting.InputItem("Thompson", 4),
                new KeyIndexedCounting.InputItem("White", 2),
                new KeyIndexedCounting.InputItem("Williams", 3),
                new KeyIndexedCounting.InputItem("Wilson", 4)
        );
        KeyIndexedCounting.InputItem[] a = list.toArray(new KeyIndexedCounting.InputItem[0]);
        KeyIndexedCounting.sort(a, 4);
        for (int i = 0; i < a.length; i++) {
            System.out.printf("%-10s %d\n", a[i].name(), a[i].key());
        }
        Assertions.assertThat(new Sorted<>(a).sorted()).isTrue();
    }
}
