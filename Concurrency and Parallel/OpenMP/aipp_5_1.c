// OpenMP Hello World.
#include <stdio.h>
#include <stdlib.h>

// 使用预处理器宏_OPENMP判断编译器是否支持OpenMP
#ifdef _OPENMP
#include <omp.h>
#endif

// 线程函数
void hello(void);

int main(int argc, char const *argv[]) {
  // 从输入获取线程数量
  int thread_count = strtol(argv[1], NULL, 10);

// pragma指令
// parallel: 指令
// num_threads: parallel指令的子句, 指定team中线程数量
#pragma omp parallel num_threads(thread_count)
  hello();

  return 0;
}

void hello(void) {
#ifdef _OPENMP
  // 获取线程ID/编号
  int my_rank = omp_get_thread_num();
  // 获取team中线程数量
  int thread_count = omp_get_num_threads();
#else
  int my_rank = 0;
  int thread_count = 1;
#endif

  printf("Hello from thread %d of %d\n", my_rank, thread_count);
}