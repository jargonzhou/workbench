package com.spike.algorithm.string;

/**
 * 以字符串为键的符号表.
 *
 * @param <Value>
 */
public interface StringST<Value> {
    // 插入键值对, val为null时删除键
    void put(String key, Value val);

    // 键对应的值, 键不存在返回null
    Value get(String key);

    // 删除键和值
    void delete(String key);

    // 是否包含键
    boolean contains(String key);

    // 符号表是否为空
    boolean isEmpty();

    // s的前缀中最长的键
    String longestPrefixOf(String s);

    // 所有以prefix为前缀的键
    Iterable<String> keysWithPrefix(String prefix);

    // 所有和pattern匹配的键: "."表示匹配任意字符
    Iterable<String> keysThatMatch(String pattern);

    // 键值对数量
    int size();

    // 所有键
    Iterable<String> keys();
}
