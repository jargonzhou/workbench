package com.spike.algorithm.adt;

import com.spike.algorithm.adt.Stack;
import org.junit.jupiter.api.Test;

public class ExpressionEvalTest {

    // Dijkstra的双栈算术表达式求值.

    // 细节:
    // 表达式由括号, 运算符和操作数(数字)组成.
    // 实现中使用了两个栈: 操作数栈, 运算符栈.

    // 从左至右依次入栈:
    // (1) 将操作数压入操作数栈;
    // (2) 将运算符压入运算符栈;
    // (3) 忽略左括号;
    // (4) 遇到右括号时, 弹出一个运算符, 弹出所需数量的操作数, 将计算结果压入操作数栈.

    void evaluate(String[] expression) {
        if (expression == null || expression.length == 0) {
            return; // do nothing
        }

        Stack<String> ops = new Stack<>(); // 运算符栈
        Stack<Double> vals = new Stack<>(); // 操作数栈

        for (String e : expression) {
            switch (e) {
                case "(":
                    break;
                case "+":
                case "-":
                case "*":
                case "/":
                case "sqrt":
                    ops.push(e);
                    break;
                case ")": {
                    String op = ops.pop();
                    double v = vals.pop();
                    switch (op) {
                        case "+":
                            v = vals.pop() + v;
                            break;
                        case "-":
                            v = vals.pop() - v;
                            break;
                        case "*":
                            v = vals.pop() * v;
                            break;
                        case "/":
                            v = vals.pop() / v;
                            break;
                        case "sqrt":
                            v = Math.sqrt(v);
                            break;
                        default:
                            break;
                    }
                    vals.push(v); // 计算结果压入操作数栈
                    break;
                }
                default: // 数字
                    vals.push(Double.parseDouble(e));
                    break;
            }
        }

        System.out.println(vals.pop()); // 最终计算结果
    }

    @Test
    public void eval() {
        // 注意: 输入的特殊编码形式
        // (1+((2+3)*(4*5)))
        String[] expression = "( 1 + ( ( 2 + 3 ) * ( 4 * 5 ) ) )".split("\\s");
        evaluate(expression);

        // ((1+sqrt(5.0))/2.0)
        expression = "( ( 1 + sqrt ( 5.0 ) ) / 2.0 )".split("\\s");
        evaluate(expression);
    }

}
