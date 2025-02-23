// 估计$\pi$.
// 参数:
//  <项数量> <线程数量>
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char* argv[]) {
  double approx;     // 最终结果
  double factor;     // 因子: (-1)^{k}
  int n;             // 项数量
  int thread_count;  // 线程数量
  double sum = 0.0;
  int k;

  n = strtol(argv[1], NULL, 10);
  thread_count = strtol(argv[2], NULL, 10);

// #pragma omp parallel for num_threads(thread_count) reduction(+ : sum)
// private(factor)

// explicit scope
#pragma omp parallel for num_threads(thread_count) default(none) \
    reduction(+ : sum) private(k, factor) shared(n)
  for (k = 0; k < n; k++) {
    if (k % 2 == 0) {
      factor = 1.0;
    } else {
      factor = -1.0;
    }
    sum += factor / (2 * k + 1);
  }
  approx = 4.0 * sum;

  printf("With n=%d terms and %d threads, estimated of pi = %.15e\n", n,
         thread_count, approx);

  return 0;
}