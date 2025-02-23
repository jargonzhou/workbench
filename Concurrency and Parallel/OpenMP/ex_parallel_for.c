// 梯形法数值积分: 使用parallel for.
// 参数: <线程数量>
// 输入: <左端点> <右端点> <梯形数量>
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

double f(double);

int main(int argc, char* argv[]) {
  double approx;     // 最终结果
  double a, b;       // 左/右端点
  int n;             // 梯形数量
  int thread_count;  // 线程数量
  double h;          // 梯形高度
  int i;

  thread_count = strtol(argv[1], NULL, 10);
  scanf("%lf %lf %d", &a, &b, &n);

  h = (b - a) / n;
  approx = (f(a) + f(b)) / 2.0;
#pragma omp parallel for num_threads(thread_count) reduction(+ : approx)
  for (i = 1; i <= n - 1; i++) {
    approx += f(a + i * h);
  }
  approx = h * approx;

  printf("With n=%d trapezoids, estimated integral from %f to %f = %.15e\n", n,
         a, b, approx);

  return 0;
}

// 被积分的函数
double f(double x) { return x * x; }