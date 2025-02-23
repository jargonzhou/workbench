// 计算斐波拉契数: task.
// 参数:
//  <项数量> <线程数量>
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

int fib(int);

int* fibs;

int main(int argc, char* argv[]) {
  int n;
  int thread_count;  // 线程数量
  int result;

  n = strtol(argv[1], NULL, 10);
  thread_count = strtol(argv[2], NULL, 10);

  fibs = malloc((n + 1) * sizeof(int));

#pragma omp parallel num_threads(thread_count)
  {
#pragma omp single
    result = fib(n);
  }

  printf("fib(%d) = %d\n", n, result);

  return 0;
}

int fib(int n) {
  int i = 0;
  int j = 0;

  if (n <= 1) {
    fibs[n] = n;
    return n;
  }

// #pragma omp task shared(i)
#pragma omp task shared(i) if (n > 20)
  i = fib(n - 1);
#pragma omp task shared(j)
  j = fib(n - 2);
#pragma omp taskwait
  fibs[n] = i + j;

  return fibs[n];
}