// 使用梯形法计算数值积分.
// 所有线程计算部分积分, 非0线程将局部结果发给线程0, 由线程0汇总.
#include <mpi.h>
#include <stdio.h>

double trap(double, double, int, double);
double f(double);

// 数值积分中梯形法
int main(void) {
  int my_rank, comm_sz, n = 1024, local_n;       // 整体/局部梯形数量,
  double a = 0.0, b = 3.0, h, local_a, local_b;  // 整体/局部端点
  double local_integral, total_integral;         // 局部/整体积分
  int source;

  MPI_Init(NULL, NULL);
  MPI_Comm_size(MPI_COMM_WORLD, &comm_sz);
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);

  h = (b - a) / n;  // 梯形高度

  // 计算局部变量: 按块划分
  local_n = n / comm_sz;
  local_a = a + my_rank * local_n * h;
  local_b = local_a + local_n * h;
  local_integral = trap(local_a, local_b, local_n, h);

  if (my_rank != 0) {
    MPI_Send(&local_integral, 1, MPI_DOUBLE, 0, 0,
             MPI_COMM_WORLD);  // 发给进程0
  } else {
    total_integral = local_integral;
    // 依次接收其他进程的消息
    for (source = 1; source < comm_sz; source++) {
      MPI_Recv(&local_integral, 1, MPI_DOUBLE, source, 0, MPI_COMM_WORLD,
               MPI_STATUS_IGNORE);
      total_integral += local_integral;
    }
  }

  // 由进程0输出
  if (my_rank == 0) {
    printf("With n=%d trapezoids, estimated integral from %f to %f = %.15e\n",
           n, a, b, total_integral);
  }

  MPI_Finalize();

  return 0;
}

// 梯形面积计算
double trap(double a,  // 左端点
            double b,  // 右端点
            int n,     // 梯形数量
            double h   // 梯形高度
) {
  double estimate, xi;
  int i;

  estimate = (f(a) + f(b)) / 2.0;
  for (i = 1; i <= n - 1; i++) {
    xi = a + i * h;
    estimate += f(xi);
  }
  estimate = estimate * h;

  return estimate;
}

// 被积分的函数
double f(double x) { return x * x; }
