// 梯形法数值积分.
// 参数: <线程数量>
// 输入: <左端点> <右端点> <梯形数量>
// 限制: 梯形数量是线程数量的整数倍
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

void trap(double, double, int, double*);
double f(double);

int main(int argc, char* argv[]) {
  double global_result = 0.0;  // 最终结果
  double a, b;                 // 左/右端点
  int n;                       // 梯形数量
  int thread_count;            // 线程数量

  thread_count = strtol(argv[1], NULL, 10);
  scanf("%lf %lf %d", &a, &b, &n);

#pragma omp parallel num_threads(thread_count)
  trap(a, b, n, &global_result);

  printf("With n=%d trapezoids, estimated integral from %f to %f = %.15e\n", n,
         a, b, global_result);

  return 0;
}

// 梯形面积计算
void trap(double a,                // 全局左端点
          double b,                // 全局右端点
          int n,                   // 全局梯形数量
          double* global_result_p  // 最终结果的指针
) {
  double h;                 // 梯形高度
  double local_a, local_b;  // 局部左/右端点
  int local_n;              // 局部梯形数量
  int i;
  double estimate, xi;

  int my_rank = omp_get_thread_num();
  int thread_count = omp_get_num_threads();

  h = (b - a) / n;
  local_n = n / thread_count;  // 限制: 梯形数量是线程数量的整数倍
  local_a = a + my_rank * local_n * h;
  local_b = local_a + local_n * h;

  estimate = (f(local_a) + f(local_b)) / 2.0;
  for (i = 1; i <= local_n - 1; i++) {
    xi = local_a + i * h;
    estimate += f(xi);
  }
  estimate = estimate * h;

  // 更新到最终结果
#pragma omp critical
  *global_result_p += estimate;
}

// 被积分的函数
double f(double x) { return x * x; }