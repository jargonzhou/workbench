package com.spike.algorithm.string;

import com.spike.algorithm.adt.Queue;

/**
 * 单词查找树.
 *
 * @param <Value>
 */
public class TrieST<Value> implements StringST<Value> {

    //
    // R = 3: 三向单词查找树, next => left, mid, right
    //

    private static int R = 256; // 基数
    private Node root;

    private static class Node {
        private Object val;
        private Node[] next = new Node[R];
    }

    public TrieST() {
        this.root = new Node();
    }

    @Override
    public void put(String key, Value val) {
        this.root = this.put(root, key, val, 0);
    }

    // 如果key存在于以x为根节点的单词查找树中, 更新关联的值
    private Node put(Node x, String key, Value val, int d) {
        if (x == null) {
            x = new Node();
        }

        if (d == key.length()) { // 长度耗尽
            x.val = val;
            return x;
        }

        char c = key.charAt(d); // 第d个字符对应的单词查找树
        x.next[c] = this.put(x.next[c], key, val, d + 1);
        return x;
    }

    @Override
    public Value get(String key) {
        Node x = this.get(root, key, 0);
        if (x == null) {
            return null;
        } else {
            return (Value) x.val;
        }
    }

    // 返回以x作为根节点的子单词查找树中与key关联的节点
    private Node get(Node x, String key, int d) {
        if (x == null) {
            return null;
        }
        if (d == key.length()) { // 长度耗尽
            return x;
        }
        char c = key.charAt(d); // 第d个字符对应的单词查找树
        return this.get(x.next[c], key, d + 1);
    }


    @Override
    public void delete(String key) {
        this.root = this.delete(root, key, 0);
    }

    private Node delete(Node x, String key, int d) {
        if (x == null) {
            return null;
        }
        if (d == key.length()) { // 长度耗尽
            x.val = null;
        } else { // 在子树中删除
            char c = key.charAt(d);
            x.next[c] = this.delete(x.next[c], key, d + 1);
        }

        // 如果x的值和链接均为空: 返回null
        // 否则返回x

        if (x.val != null) {
            return x;
        }

        for (char c = 0; c < R; c++) {
            if (x.next[c] != null) {
                return x;
            }
        }
        return null;
    }

    @Override
    public boolean contains(String key) {
        return this.get(key) != null;
    }

    @Override
    public boolean isEmpty() {
        return this.size() > 0;
    }

    @Override
    public String longestPrefixOf(String s) {
        int length = this.search(root, s, 0, 0);
        return s.substring(0, length);
    }

    private int search(Node x, String s, int d, int length) {
        if (x == null) {
            return length;
        }

        if (x.val != null) {
            length = d;
        }

        if (d == s.length()) { // 长度耗尽
            return length;
        }

        char c = s.charAt(d);
        return this.search(x.next[c], s, d + 1, length);
    }

    @Override
    public Iterable<String> keysWithPrefix(String prefix) {
        Queue<String> q = new Queue<>();
        this.collect(this.get(root, prefix, 0), prefix, q);
        return q;
    }

    private void collect(Node x, String prefix, Queue<String> q) {
        if (x == null) {
            return;
        }
        if (x.val != null) { // 值存在时入队
            q.enqueue(prefix);
        }
        for (char c = 0; c < R; c++) {
            this.collect(x.next[c], prefix + c, q);
        }
    }


    @Override
    public Iterable<String> keysThatMatch(String pattern) {
        Queue<String> q = new Queue<>();
        this.collect(root, "", pattern, q);
        return q;
    }

    private void collect(Node x, String prefix, String pattern, Queue<String> q) {
        int d = prefix.length();
        if (x == null) {
            return;
        }
        if (d == pattern.length() && x.val != null) { // 长度匹配, 值存在时: 入队
            q.enqueue(prefix);
        }
        if (d == pattern.length()) { // 模式长度耗尽
            return;
        }

        char next = pattern.charAt(d);
        for (char c = 0; c < R; c++) {
            if (next == '.' || next == c) { // 字符匹配
                this.collect(x.next[c], prefix + c, pattern, q);
            }
        }
    }

    @Override
    public int size() {
        return this.size(root);
    }

    // 延时递归实现
    private int size(Node x) {
        if (x == null) {
            return 0;
        }

        int cnt = 0;
        if (x.val != null) { // 值不为null
            cnt++;
        }
        for (char c = 0; c < R; c++) {
            cnt += size(x.next[c]);
        }
        return cnt;
    }


    @Override
    public Iterable<String> keys() {
        return this.keysWithPrefix("");
    }
}
