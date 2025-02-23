// 由线程0获取输入, 并发送给其他线程.
#include <mpi.h>
#include <stdio.h>

// 函数声明
double trap(double, double, int, double);
double f(double);
void get_input(int my_rank, int comm_sz, double *a_p, double *b_p, int *n_p);

// 数值积分中梯形规则
int main(void) {
  // int my_rank, comm_sz, n = 1024, local_n;       // 整体/局部梯形数量,
  // double a = 0.0, b = 3.0, h, local_a, local_b;  // 整体/局部端点
  // 使用输入获取a, b, n
  int my_rank, comm_sz, n, local_n;       // 整体/局部梯形数量,
  double a, b, h, local_a, local_b;       // 整体/局部端点
  double local_integral, total_integral;  // 局部/整体积分
  int source;

  MPI_Init(NULL, NULL);
  MPI_Comm_size(MPI_COMM_WORLD, &comm_sz);
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);

  // 获取输入
  get_input(my_rank, comm_sz, &a, &b, &n);

  h = (b - a) / n;  // 梯形高度

  // 计算局部变量
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

//
// add to aipp_3_2.c
//
void get_input(int my_rank, int comm_sz, double *a_p, double *b_p, int *n_p) {
  int dest;

  if (my_rank == 0) {
    printf("Enter a, b, and n\n");
    scanf("%lf %lf %d", a_p, b_p, n_p);
    // 依次发送a, b, n
    for (dest = 1; dest < comm_sz; dest++) {
      MPI_Send(a_p, 1, MPI_DOUBLE, dest, 0, MPI_COMM_WORLD);
      MPI_Send(b_p, 1, MPI_DOUBLE, dest, 0, MPI_COMM_WORLD);
      MPI_Send(n_p, 1, MPI_INT, dest, 0, MPI_COMM_WORLD);
    }
  } else {
    // 进程0之外的进程接收a, b, n
    MPI_Recv(a_p, 1, MPI_DOUBLE, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    MPI_Recv(b_p, 1, MPI_DOUBLE, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    MPI_Recv(n_p, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  }
}