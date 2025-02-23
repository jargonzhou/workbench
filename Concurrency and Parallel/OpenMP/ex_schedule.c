// 调度示例: 将循环中迭代指派给线程.
// 参数:
// <项数量> <线程数量>
#include <math.h>
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

double f(int);

int main(int argc, char* argv[]) {
  int n;             // 项数量
  int thread_count;  // 线程数量
  double sum = 0.0;
  int i;

  n = strtol(argv[1], NULL, 10);
  thread_count = strtol(argv[2], NULL, 10);

// #pragma omp parallel for num_threads(thread_count) reduction(+ : sum)
// cyclic schedule
#pragma omp parallel for num_threads(thread_count) reduction(+ : sum) \
    schedule(static, 1)
  for (i = 0; i <= n; i++) {
    sum += f(i);
  }

  printf("With %d threads, sum = %.15e\n", thread_count, sum);

  return 0;
}

// 示例: i越大, 所需计算量越大.
double f(int i) {
  int j, start = i * (i + 1) / 2, finish = start + i;
  double return_val = 0.0;

  for (j = start; j <= finish; j++) {
    return_val += sin(j);
  }

  return return_val;
}