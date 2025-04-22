package com.spike.algorithm.searching;

import com.google.common.base.Strings;
import com.spike.algorithm.adt.Queue;
import com.spike.algorithm.searching.core.OST;
import com.spike.algorithm.support.io.StdOut;

import javax.annotation.Nonnull;
import java.util.Iterator;

/**
 * 红黑树.
 * <pre>
 * 两种链接: 红链接将两个2-节点连接起来构成一个3-节点(将红链接拉平), 黑链接是2-3树中普通链接.
 *
 * 红黑树是含有红黑链接的二叉查找树, 且:
 * (1) 红链接均为左链接;
 * (2) 没有一个节点同时和两条红链接相连;
 * (3) 完美黑色平衡的: 任意空链接到根节点的路径上的黑链接数量相同.
 *
 * 旋转操作: 操作中可能会出现红色右链接或者两条连续的红链接, 需要旋转修复.
 * (1) 左旋转: 将一条红右链接转化为左链接;
 * (2) 右旋转: 将一条红左链接转化为右链接.
 * 保持: 有序性和完美平衡性.
 *
 * 颜色翻转: 一个节点的左右子树链接均为红链接
 * (1) 将子节点的颜色由红变黑;
 * (2) 将父节点的颜色由黑变红.
 * 保持: 黑色平衡性.
 * </pre>
 */
public class RedBlackBST<Key extends Comparable<Key>, Value> implements OST<Key, Value> {

    private static final boolean RED = true;
    private static final boolean BLACK = false;

    private class Node {
        private Key key; // 键
        private Value val; // 值
        private Node left, right; // 左右子树

        // 父节点指向该节点的链接的颜色, 即节点的颜色为指向该节点的链接的颜色;
        // 空链接为黑色
        private boolean color;

        private int N; // 以该节点为根的子树中节点总数

        public Node(Key key, Value val, boolean color, int N) {
            this.key = key;
            this.val = val;
            this.color = color;
            this.N = N;
        }
    }

    private Node root; // 根节点

    public RedBlackBST() {
    }

    //
    // 插入
    //

    @Override
    public void put(Key key, Value val) {
        if (key == null) {
            throw new IllegalArgumentException("null key");
        }
        if (val == null) {
            this.delete(key);
            return;
        }

        root = this.put(root, key, val);

        // 每次插入后, 将根节点置为黑色
        root.color = BLACK;
    }

    // 子树h中插入键值对
    private Node put(Node h, Key key, Value val) {
        if (h == null) {
            return new Node(key, val, RED, 1); // 和父节点用红链接相连
        }

        int cmp = key.compareTo(h.key);
        if (cmp < 0) {// 插入左子树
            h.left = this.put(h.left, key, val);
        } else if (cmp > 0) {// 插入右子树
            h.right = this.put(h.right, key, val);
        } else { // 更新值
            h.val = val;
        }

        // 先处理右红链接: 左旋
        if (this.isRed(h.right) && !this.isRed(h.left)) {
            h = this.rotateLeft(h);
        }
        // 连续两条左红链接: 右旋 + 颜色翻转
        if (this.isRed(h.left) && this.isRed(h.left.left)) {
            h = this.rotateRight(h);
        }
        // 左右红链接: 颜色翻转
        if (this.isRed(h.left) && this.isRed(h.right)) {
            this.flipColor(h);
        }

        h.N = this.size(h.left) + this.size(h.right) + 1;
        return h;
    }

    // 翻转节点和其子节点的颜色
    // 例: 子节点由红变黑, 父节点由黑变红
    // PRE: 节点和其子节点的颜色相反
    private void flipColor(Node h) {
        h.color = !h.color;
        h.left.color = !h.left.color;
        h.right.color = !h.right.color;
    }

    //
    // 搜索
    //

    @Override
    public Value get(Key key) {
        if (key == null) {
            throw new IllegalArgumentException("null key");
        }

        return this.get(root, key);
    }

    // 在子树x中查找
    private Value get(Node x, Key key) {
        while (x != null) {
            int cmp = key.compareTo(x.key);
            if (cmp < 0) { // 左子树
                x = x.left;
            } else if (cmp > 0) { // 右子树
                x = x.right;
            } else {
                return x.val;
            }
        }
        return null;
    }

    @Override
    public boolean contains(Key key) {
        return this.get(key) != null;
    }

    //
    // 删除
    //

    // 删除最小键
    // 沿着左连接向下进行变换, 确保当前节点不是2-节点.
    // (1) 当前节点的左子节点不是2-节点: 结束;
    // (2) 当前节点的左子节点是2-节点, 右子节点不是2-节点, 将右子节点中的一个键移动到左子节点中;
    // (3) 当前节点的左子节点和右子节点都是2-节点, 将父节点和左右子节点合并成4-节点.
    // 最终含有最小键的3-节点/4-节点: 直接从中删除.
    // 然后向上分解所有临时的4-节点.
    @Override
    public void deleteMin() {
        if (this.isEmpty()) {
            throw new IllegalStateException("empty!");
        }
        // 根节点的左右子链接均为黑色(这时当前节点是2-节点), 将根节点置为红色
        if (!this.isRed(root.left) && !this.isRed(root.right)) {
            root.color = RED;
        }

        root = this.deleteMin(root);

        if (!this.isEmpty()) { // 非空树的根节点置为黑丝
            root.color = BLACK;
        }
    }

    // PRE: 当前节点不是2-节点
    private Node deleteMin(Node h) {
        if (h.left == null) {
            return null;
        }

        // 当前节点的左子节点是2-节点
        if (!this.isRed(h.left) && !this.isRed(h.left.left)) {
            h = this.moveRedLeft(h);
        }

        h.left = this.deleteMin(h.left); // 沿着左链接

        return this.balance(h);
    }

    // 保持平衡
    private Node balance(Node h) {

        // 红右链接
        if (this.isRed(h.right)) {
            h = this.rotateLeft(h);
        }
        // 连续的红左链接
        if (this.isRed(h.left) && this.isRed(h.left.left)) {
            h = this.rotateRight(h);
        }
        // 左右子链接均为红色
        if (this.isRed(h.left) && this.isRed(h.right)) {
            this.flipColor(h);
        }

        h.N = size(h.left) + size(h.right) + 1;
        return h;
    }

    // PRE: h为红色, h.left, h.left.left为黑色 - 当前节点的左子节点是2-节点
    // POST: h.left或者其子节点置为红色
    private Node moveRedLeft(Node h) {
        // PRE: h.right == BLACK
        this.flipColor(h);
        // POST: h.right == RED

        // 当前节点的右子节点不是2-节点时: 借
        if (this.isRed(h.right.left)) {
            h.right = this.rotateRight(h.right); // 右子节点右旋转
            h = this.rotateLeft(h); // 左旋转
            this.flipColor(h); // 颜色翻转
        }
        return h;
    }

    // 删除键
    // 沿着左链确保查找过程中任意当前节点不是2-节点.
    // (1) 被查找的键在树的底部: 直接删除.
    // (2) 不在树的底部: 与二叉查找树一样, 将它和其右子树中的后继节点交换: 在右子树中删除最小键.
    // 然后向上分解所有临时的4-节点.
    @Override
    public void delete(Key key) {
        if (this.isEmpty()) {
            throw new IllegalStateException("empty!");
        }

        if (!this.contains(key)) {
            return;
        }

        // 如果根节点的左右子链接均为黑色, 将根节点置为红色
        if (!this.isRed(root.left) && !this.isRed(root.right)) {
            root.color = RED;
        }

        root = this.delete(root, key);

        if (!this.isEmpty()) {
            root.color = BLACK;
        }
    }

    // 在子树h中删除
    private Node delete(Node h, Key key) {
        if (key.compareTo(h.key) < 0) {
            if (!this.isRed(h.left) && !this.isRed(h.left.left)) {
                h = moveRedLeft(h);
            }
            h.left = this.delete(h.left, key);

        } else {
            if (this.isRed(h.left)) {
                h = this.rotateRight(h);
            }
            if (key.compareTo(h.key) == 0 && (h.right == null)) {
                return null;
            }
            if (!this.isRed(h.right) && !this.isRed(h.right.left)) {
                h = this.moveRedRight(h);
            }
            if (key.compareTo(h.key) == 0) {
                Node x = this.min(h.right);
                h.key = x.key;
                h.val = x.val;
                h.right = this.deleteMin(h.right);
            } else {
                h.right = this.delete(h.right, key);
            }
        }

        return this.balance(h);
    }


    // PRE: h为红色, h.right, h.right.left为黑色
    // POST: h.right或者其子节点置为红色
    private Node moveRedRight(Node h) {
        this.flipColor(h);
        if (this.isRed(h.left.left)) {
            h = this.rotateRight(h);
            this.flipColor(h);
        }
        return h;
    }


    @Override
    public void deleteMax() {
        if (this.isEmpty()) {
            throw new IllegalStateException("empty!");
        }
        // 左右子链接均为黑色, 将根节点置为红色
        if (!this.isRed(root.left) && !this.isRed(root.right)) {
            root.color = RED;
        }

        root = this.deleteMax(root);

        if (!this.isEmpty()) {
            root.color = BLACK;
        }
    }

    private Node deleteMax(Node h) {
        if (this.isRed(h.left)) {
            h = this.rotateRight(h);
        }

        if (h.right == null) {
            return null;
        }

        if (!this.isRed(h.right) && !this.isRed(h.right.left)) {
            h = moveRedRight(h);
        }

        h.right = this.deleteMax(h.right);

        return this.balance(h);
    }

    //
    // 辅助方法
    //

    // 是否为红链入节点
    private boolean isRed(Node x) {
        if (x == null) { // 空链接为黑色
            return false;
        }
        return x.color == RED;
    }

    @Override
    public int size() {
        return this.size(root);
    }

    private int size(Node x) {
        if (x == null) {
            return 0;
        }
        return x.N;
    }

    @Override
    public boolean isEmpty() {
        return root == null;
    }

    // 左旋h的右链接, 返回旋转后的根节点
    // PRE: h.right == RED
    private Node rotateLeft(Node h) {
        Node x = h.right;

        h.right = x.left;
        x.left = h;

        x.color = h.color; // 保持子树'根'节点颜色不变
        h.color = RED;

        x.N = h.N;
        h.N = 1 + this.size(h.left) + this.size(h.right);

        return x; // 子树'根'节点
    }

    // 右旋h的左链接, 返回旋转后的根节点
    // PRE: x.left == RED
    private Node rotateRight(Node h) {
        Node x = h.left;

        h.left = x.right;
        x.right = h;

        x.color = h.color;
        h.color = RED;

        x.N = h.N;
        h.N = 1 + this.size(h.left) + this.size(h.right);

        return x;
    }

    public void dump() {
        this.print(root, 0);
    }

    private void print(Node x, int level) {
        if (x == null) {
            return;
        }

        // 中序遍历
        this.print(x.left, level + 1);
        System.out.println(Strings.repeat(" ", level) + x.key + "(" + x.val + ")");
        this.print(x.right, level + 1);
    }


    @Override
    public @Nonnull Iterator<Key> iterator() {
        return keys().iterator();
    }

    //
    // ordered symbol table
    //

    @Override
    public Key min() {
        if (this.isEmpty()) {
            throw new IllegalStateException("empty!");
        }
        return this.min(root).key;
    }

    // 以x为根的子树中最小键节点
    private Node min(Node x) {
        if (x.left == null) { // 直到左链接为空
            return x;
        } else {
            return this.min(x.left);
        }
    }

    @Override
    public Key max() {
        if (this.isEmpty()) {
            throw new IllegalStateException("empty!");
        }
        return this.max(root).key;
    }

    private Node max(Node x) {
        if (x.right == null) {// 直到右链接为空
            return x;
        } else {
            return this.max(x.right);
        }
    }

    @Override
    public Key floor(Key key) {
        if (key == null) {
            throw new IllegalArgumentException("null key");
        }
        if (this.isEmpty()) {
            throw new IllegalStateException("empty!");
        }

        Node x = this.floor(root, key);
        if (x == null) {
            return null;
        } else {
            return x.key;
        }
    }

    private Node floor(Node x, Key key) {
        if (x == null) {
            return null;
        }

        int cmp = key.compareTo(x.key);
        if (cmp == 0) {
            return x;
        } else if (cmp < 0) {
            return this.floor(x.left, key);
        } else {
            Node t = this.floor(x.right, key);
            if (t != null) {
                return t;
            } else {
                return x;
            }
        }
    }

    @Override
    public Key ceiling(Key key) {
        if (key == null) {
            throw new IllegalArgumentException("null key");
        }
        if (this.isEmpty()) {
            throw new IllegalStateException("empty!");
        }
        Node x = this.ceiling(root, key);
        if (x == null) {
            return null;
        } else {
            return x.key;
        }
    }

    private Node ceiling(Node x, Key key) {
        if (x == null) {
            return null;
        }
        int cmp = key.compareTo(x.key);
        if (cmp == 0) {
            return x;
        } else if (cmp > 0) {
            return ceiling(x.right, key);
        } else {
            Node t = ceiling(x.left, key);
            if (t != null) {
                return t;
            } else {
                return x;
            }
        }
    }

    @Override
    public int rank(Key key) {
        if (key == null) {
            throw new IllegalArgumentException("null key");
        }
        return this.rank(key, root);
    }

    private int rank(Key key, Node x) {
        if (x == null) {
            return 0;
        }
        int cmp = key.compareTo(x.key);
        if (cmp < 0) {
            return this.rank(key, x.left);
        } else if (cmp > 0) {
            return 1 + this.size(x.left) + this.rank(key, x.right);
        } else {
            return this.size(x.left);
        }
    }

    @Override
    public Key select(int k) {
        if (k <= 0 || k >= this.size()) {
            throw new IllegalArgumentException("invalid argument!");
        }

        Node x = this.select(root, k);
        return x.key;
    }

    private Node select(Node x, int k) {
        int t = this.size(x.left);
        if (t > k) {
            return this.select(x.left, k);
        } else if (t < k) {
            return this.select(x.right, k - t - 1);
        } else {
            return x;
        }
    }

    //
    // range
    //

    @Override
    public Iterable<Key> keys() {
        if (this.isEmpty()) {
            return new Queue<>();
        }
        return this.keys(this.min(), this.max());
    }

    @Override
    public int size(Key low, Key high) {

        if (low == null) {
            throw new IllegalArgumentException("null low!");
        }
        if (high == null) {
            throw new IllegalArgumentException("null high!");
        }

        if (low.compareTo(high) > 0) {
            return 0;
        }
        if (this.contains(high)) {
            return this.rank(high) - this.rank(low) + 1;
        } else {
            return this.rank(high) - this.rank(low);
        }
    }

    @Override
    public Iterable<Key> keys(Key low, Key high) {

        if (low == null) {
            throw new IllegalArgumentException("null low!");
        }
        if (high == null) {
            throw new IllegalArgumentException("null high!");
        }

        Queue<Key> queue = new Queue<>();
        this.keys(root, queue, low, high);
        return queue;
    }


    private void keys(Node x, Queue<Key> queue, Key lo, Key hi) {
        if (x == null) {
            return;
        }
        int cmplo = lo.compareTo(x.key);
        int cmphi = hi.compareTo(x.key);
        if (cmplo < 0) {
            this.keys(x.left, queue, lo, hi);
        }
        if (cmplo <= 0 && cmphi >= 0) {
            queue.enqueue(x.key);
        }
        if (cmphi > 0) {
            this.keys(x.right, queue, lo, hi);
        }
    }

    //
    // 检查工具
    //

    private boolean check() {
        if (!isBST()) StdOut.println("Not in symmetric order");
        if (!isSizeConsistent()) StdOut.println("Subtree counts not consistent");
        if (!isRankConsistent()) StdOut.println("Ranks not consistent");
        if (!is23()) StdOut.println("Not a 2-3 tree");
        if (!isBalanced()) StdOut.println("Not balanced");
        return isBST() && isSizeConsistent() && isRankConsistent() && is23() && isBalanced();
    }

    // does this binary tree satisfy symmetric order?
    // Note: this test also ensures that data structure is a binary tree since order is strict
    private boolean isBST() {
        return isBST(root, null, null);
    }

    // is the tree rooted at x a BST with all keys strictly between min and max
    // (if min or max is null, treat as empty constraint)
    // Credit: elegant solution due to Bob Dondero
    private boolean isBST(Node x, Key min, Key max) {
        if (x == null) return true;
        if (min != null && x.key.compareTo(min) <= 0) return false;
        if (max != null && x.key.compareTo(max) >= 0) return false;
        return isBST(x.left, min, x.key) && isBST(x.right, x.key, max);
    }

    // are the size fields correct?
    private boolean isSizeConsistent() {
        return isSizeConsistent(root);
    }

    private boolean isSizeConsistent(Node x) {
        if (x == null) return true;
        if (x.N != size(x.left) + size(x.right) + 1) return false;
        return isSizeConsistent(x.left) && isSizeConsistent(x.right);
    }

    // check that ranks are consistent
    private boolean isRankConsistent() {
        for (int i = 0; i < size(); i++)
            if (i != rank(select(i))) return false;
        for (Key key : keys())
            if (key.compareTo(select(rank(key))) != 0) return false;
        return true;
    }

    // Does the tree have no red right links, and at most one (left)
    // red links in a row on any path?
    private boolean is23() {
        return is23(root);
    }

    private boolean is23(Node x) {
        if (x == null) return true;
        if (isRed(x.right)) return false;
        if (x != root && isRed(x) && isRed(x.left))
            return false;
        return is23(x.left) && is23(x.right);
    }

    // do all paths from root to leaf have same number of black edges?
    private boolean isBalanced() {
        int black = 0;     // number of black links on path from root to min
        Node x = root;
        while (x != null) {
            if (!isRed(x)) black++;
            x = x.left;
        }
        return isBalanced(root, black);
    }

    // does every path from the root to a leaf have the given number of black links?
    private boolean isBalanced(Node x, int black) {
        if (x == null) return black == 0;
        if (!isRed(x)) black--;
        return isBalanced(x.left, black) && isBalanced(x.right, black);
    }
}