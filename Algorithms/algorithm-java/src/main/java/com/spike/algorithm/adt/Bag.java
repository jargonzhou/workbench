package com.spike.algorithm.adt;

import javax.annotation.Nonnull;
import java.util.Iterator;

/**
 * 袋: 元素无序可重复.
 */
public class Bag<Item> implements Iterable<Item> {
    private Node<Item> first;// 链表头部节点
    private int N = 0; // 元素数量

    /**
     * 节点: 基于链表的实现.
     */
    private static class Node<Item> {
        private Item item;
        private Node<Item> next;
    }

    private class BagIterator implements Iterator<Item> {
        private Node<Item> current;

        BagIterator(Node<Item> start) {
            current = start;
        }

        @Override
        public boolean hasNext() {
            return current != null;
        }

        @Override
        public Item next() {
            Item item = current.item;
            current = current.next;
            return item;
        }
    }


    @Override
    public @Nonnull Iterator<Item> iterator() {
        return new BagIterator(first);
    }

    /**
     * 构造空袋.
     */
    public Bag() {
    }

    /**
     * 添加一个元素.
     */
    public void add(Item item) {
        // 从链表头部添加元素
        Node<Item> oldFirst = first;
        first = new Node<>();
        first.item = item;
        first.next = oldFirst;

        N++;
    }

    /**
     * 是否为空袋.
     */
    public boolean isEmpty() {
        return N == 0;
    }

    /**
     * 袋中元素数量.
     */
    public int size() {
        return N;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Bag[ ");
        for (Node<Item> x = first; x != null; x = x.next) {
            sb.append(x.item).append(" ");
        }
        sb.append("]");
        return sb.toString();
    }
}
