package com.spike.algorithm.problems.list;

// 复杂链表的复制
public class O35 {

    public static void main(String[] args) {
        O35 o35 = new O35();

        ComplexListNode A = new ComplexListNode('A');
        ComplexListNode B = new ComplexListNode('B');
        ComplexListNode C = new ComplexListNode('C');
        ComplexListNode D = new ComplexListNode('D');
        ComplexListNode E = new ComplexListNode('E');
        A.next = B;
        B.next = C;
        C.next = D;
        D.next = E;
        A.random = C;
        B.random = E;
        D.random = B;
        // A[C] B[E] C D[B] E
        ComplexListNode.traverse(A, v -> String.valueOf((char) v.intValue()));

        ComplexListNode result = o35.deepCopy(A);
        // A[C] B[E] C D[B] E
        ComplexListNode.traverse(A, v -> String.valueOf((char) v.intValue()));
    }

    public ComplexListNode deepCopy(ComplexListNode x) {
        if (x == null) {
            return null;
        }

        // 在之前的链表上复制, 每个节点都复制一个节点跟在后面
        ComplexListNode t = x;
        while (t != null) {
            // 拷贝节点
            ComplexListNode c = new ComplexListNode(t.val);
            c.next = t.next;

            t.next = c;
            // 步进
            t = c.next;
        }

        // 复制random节点
        t = x;
        while (t != null) {
            ComplexListNode c = t.next; // 复制的节点
            if (t.random != null) {
                c.random = t.random.next; // 在下一个节点上
            }
            // 步进
            t = c.next;
        }

        // 将复制的新节点连接起来
        t = x;
        ComplexListNode result = null;
        ComplexListNode c = null; // 复制的节点
        if (t != null) {
            result = t.next;
            c = t.next;

            // 步进
            t.next = c.next;
            t = t.next;
        }
        while (t != null) {
            c.next = t.next;
            c = c.next;

            t.next = c.next;
            t = t.next;
        }

        return result;
    }
}
