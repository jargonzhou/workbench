#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

// 线程数量
int thread_count;

// 线程函数
void* hello(void* rank);

int main(int argc, char* argv[]) {
  long t_idx;
  pthread_t* pts;  // 线程标识符/句柄

  // 从输入读取线程数量
  thread_count = strtol(argv[1], NULL, 10);

  // 分配线程句柄内存
  pts = malloc(thread_count * sizeof(pthread_t));

  // 依次创建线程
  for (t_idx = 0; t_idx < thread_count; t_idx++) {
    pthread_create(&pts[t_idx],  // OUT: pthread_t *
                   NULL,         // 线程属性: pthread_attr_t *
                   hello,        // 线程函数: void *(*)(void *)
                   (void*)t_idx  // 线程函数参数: void *
    );
  }

  printf("Hello from main thread\n");

  // 等待线程结束
  for (t_idx = 0; t_idx < thread_count; t_idx++) {
    pthread_join(pts[t_idx],  // 线程: pthread_t
                 NULL         // 返回值: void **
    );
  }

  // 清理
  free(pts);
}

void* hello(void* rank /* 自定义线程序号 */) {
  long my_rank = (long)rank;
  printf("Hello from thread %ld of %d\n", my_rank, thread_count);
  return NULL;
}