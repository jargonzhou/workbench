// 奇偶排序.
// 参数:
//  <线程数量>
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char* argv[]) {
  int a[] = {9, 7, 8, 6};  // 待排序数组
  int n;                   // 数组大小
  int phase;               // 阶段
  int i;
  int tmp;
  int thread_count;  // 线程数量

  n = 4;

  thread_count = strtol(argv[1], NULL, 10);

  // use: parallel for
  //   for (phase = 0; phase < n; phase++) {
  //     if (phase % 2 == 0) {
  // #pragma omp parallel for num_threads(thread_count) default(none)
  //     shared(a, n) private(i, tmp)
  //       for (i = 1; i < n; i += 2) {
  //         if (a[i - 1] > a[i]) {
  //           tmp = a[i - 1];
  //           a[i - 1] = a[i];
  //           a[i] = tmp;
  //         }
  //       }
  //     } else {
  // #pragma omp parallel for num_threads(thread_count) default(none)
  //     shared(a, n) private(i, tmp)
  //       for (i = 1; i < n - 1; i += 2) {
  //         if (a[i] > a[i + 1]) {
  //           tmp = a[i + 1];
  //           a[i + 1] = a[i];
  //           a[i] = tmp;
  //         }
  //       }
  //     }
  //   }

  // use: parallel + for
#pragma omp parallel num_threads(thread_count) default(none) \
    shared(a, n) private(i, tmp, phase)
  for (phase = 0; phase < n; phase++) {
    if (phase % 2 == 0) {
#pragma omp for
      for (i = 1; i < n; i += 2) {
        if (a[i - 1] > a[i]) {
          tmp = a[i - 1];
          a[i - 1] = a[i];
          a[i] = tmp;
        }
      }
    } else {
#pragma omp for
      for (i = 1; i < n - 1; i += 2) {
        if (a[i] > a[i + 1]) {
          tmp = a[i + 1];
          a[i + 1] = a[i];
          a[i] = tmp;
        }
      }
    }
  }

  printf("With %d threads, result = ", thread_count);
  for (i = 0; i < n; i++) {
    printf("%d ", a[i]);
  }
  printf("\n");

  return 0;
}