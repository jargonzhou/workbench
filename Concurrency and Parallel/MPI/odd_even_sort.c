// MPI奇偶排序.
//  1. 各线程随机生成局部数组.
//  2. 奇偶排序: .
//  3. 按线程rank输出所有局部数组.
#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const int RMAX = 100;

// 函数声明
void gen_list(int local_a[], int local_n, int my_rank);
void print_local_lists(int local_a[], int local_n, int my_rank, int comm_sz,
                       MPI_Comm comm);
void print_list(int local_a[], int local_n, int rank);
void print_global_list(int local_a[], int local_n, int my_rank, int comm_sz,
                       MPI_Comm comm);
int compare(const void* a, const void* b);
void odd_even_sort(int local_a[], int local_n, int my_rank, int comm_sz,
                   MPI_Comm comm);
void odd_even_sort_step(int local_a[], int temp_b[], int temp_c[], int local_n,
                        int phase, int even_partner, int odd_partner,
                        int my_rank, int comm_sz, MPI_Comm comm);
void merge_low(int my_keys[], int recv_keys[], int temp_keys[], int local_n);
void merge_high(int local_a[], int temp_b[], int temp_c[], int local_n);

int main(int argc, char* argv[]) {
  int my_rank, comm_sz;
  int local_n = 10;
  MPI_Comm comm = MPI_COMM_WORLD;
  int* local_a;

  MPI_Init(NULL, NULL);
  MPI_Comm_size(comm, &comm_sz);
  MPI_Comm_rank(comm, &my_rank);

  // 生成局部数组
  local_a = (int*)malloc(local_n * sizeof(int));
  gen_list(local_a, local_n, my_rank);
  print_local_lists(local_a, local_n, my_rank, comm_sz, comm);

  // 排序
  odd_even_sort(local_a, local_n, my_rank, comm_sz, comm);

  // 输出
  print_global_list(local_a, local_n, my_rank, comm_sz, comm);

  free(local_a);

  MPI_Finalize();

  return 0;
}

void gen_list(int local_a[], int local_n, int my_rank) {
  int i;

  srandom(my_rank + 1);
  for (i = 0; i < local_n; i++) {
    local_a[i] = random() % RMAX;
  }
}

void print_local_lists(int local_a[], int local_n, int my_rank, int comm_sz,
                       MPI_Comm comm) {
  int* a;
  int i;

  MPI_Status status;

  // 由线程0接收其他线程的局部数组
  if (my_rank == 0) {
    a = (int*)malloc(local_n * sizeof(int));
    print_list(local_a, local_n, my_rank);

    for (i = 1; i < comm_sz; i++) {
      MPI_Recv(a, local_n, MPI_INT, /* source */ i, /* tag */ 0, comm, &status);
      print_list(a, local_n, i);
    }
    free(a);
  } else {
    MPI_Send(local_a, local_n, MPI_INT, /* dest */ 0, /* tag */ 0, comm);
  }
}

// 打印数组.
void print_list(int local_a[], int local_n, int rank) {
  int i;

  printf("%d: ", rank);
  for (i = 0; i < local_n; i++) {
    printf("%d ", local_a[i]);
  }
  printf("\n");
}

// 打印全局数组.
void print_global_list(int local_a[], int local_n, int my_rank, int comm_sz,
                       MPI_Comm comm) {
  int* a = NULL;
  int n;
  int i;

  // 由线程0收集所有局部数组
  if (my_rank == 0) {
    n = comm_sz * local_n;
    a = (int*)malloc(n * sizeof(int));
    MPI_Gather(/* sendbuf */ local_a, local_n, MPI_INT, /* recvbuf */ a,
               local_n, MPI_INT, /* root */ 0, comm);
    printf("Global list: ");
    for (i = 0; i < n; i++) {
      printf("%d ", a[i]);
    }
    printf("\n");
    free(a);
  } else {
    MPI_Gather(local_a, local_n, MPI_INT, a, local_n, MPI_INT, 0, comm);
  }
}

// int比较函数.
int compare(const void* a, const void* b) { return (*(int*)a - *(int*)b); }

// 排序
void odd_even_sort(int local_a[], int local_n, int my_rank, int comm_sz,
                   MPI_Comm comm) {
  int phase;
  int *temp_b, *temp_c;
  int even_partner;  // even phase partner
  int odd_partner;   // odd phase partner

  temp_b = (int*)malloc(local_n * sizeof(int));
  temp_c = (int*)malloc(local_n * sizeof(int));

  // comment: rank as data
  // data: 0,1,2,3
  // rank: 0,1,2,3

  if (my_rank % 2 != 0) {        // odd rank: ex 1
    even_partner = my_rank - 1;  // 0-1
    odd_partner = my_rank + 1;   // 1-2
    // if (odd_partner == comm_sz) odd_partner = MPI_PROC_NULL;
  } else {                       // even rank: ex 0
    even_partner = my_rank + 1;  // 0-1
    // if (even_partner == comm_sz) even_partner = MPI_PROC_NULL;
    odd_partner = my_rank - 1;  // -1-0
  }
  if (odd_partner == -1 || odd_partner == comm_sz) {
    odd_partner = MPI_PROC_NULL;
  }
  if (even_partner == -1 || even_partner == comm_sz) {
    even_partner = MPI_PROC_NULL;
  }

  // 局部排序
  qsort(local_a, local_n, sizeof(int), compare);

  // 按阶段执行排序步骤
  for (phase = 0; phase < comm_sz; phase++) {
    odd_even_sort_step(local_a, temp_b, temp_c, local_n, phase, even_partner,
                       odd_partner, my_rank, comm_sz, comm);
  }
}

// 伪码: 计算通信端
// void calc_partner() {
//   if (phase % 2 == 0) {      // even phase
//     if (my_rank % 2 != 0) {  // odd rank
//       partner = my_rank - 1;
//     } else {  // even rank
//       partner = my_rank + 1;
//     }
//   } else {                   // odd phase
//     if (my_rank % 2 != 0) {  // odd rank
//       partner = my_rank + 1;
//     } else {  // even rank
//       partner = my_rank - 1;
//     }
//   }

//   if (partner == -1 || partner == comm_sz) {
//     partner = MPI_PROC_NULL;
//   }
// }

void odd_even_sort_step(int local_a[], int temp_b[], int temp_c[], int local_n,
                        int phase, int even_partner, int odd_partner,
                        int my_rank, int comm_sz, MPI_Comm comm) {
  MPI_Status status;

  if (phase % 2 == 0) {       // even phase
    if (even_partner >= 0) {  // MPI_PROC_NULL = -2
      MPI_Sendrecv(/* sendbuf */ local_a, local_n, MPI_INT,
                   /* dest */ even_partner, 0,
                   /* recvbuf */ temp_b, local_n, MPI_INT,
                   /* source */ even_partner, 0, comm, &status);
      if (my_rank % 2 != 0)
        merge_high(local_a, temp_b, temp_c, local_n);
      else
        merge_low(local_a, temp_b, temp_c, local_n);
    }
  } else {  // odd phase
    if (odd_partner >= 0) {
      MPI_Sendrecv(local_a, local_n, MPI_INT, odd_partner, 0,  //
                   temp_b, local_n, MPI_INT, odd_partner, 0, comm, &status);
      if (my_rank % 2 != 0)
        merge_low(local_a, temp_b, temp_c, local_n);
      else
        merge_high(local_a, temp_b, temp_c, local_n);
    }
  }
}

// my_keys中收集较小的值.
void merge_low(int my_keys[],    // in/out
               int recv_keys[],  // in
               int temp_keys[],  // 临时数组
               int local_n) {
  int m_i, r_i, t_i;

  m_i = r_i = t_i = 0;
  while (t_i < local_n) {
    if (my_keys[m_i] <= recv_keys[r_i]) {
      temp_keys[t_i] = my_keys[m_i];
      t_i++;
      m_i++;
    } else {
      temp_keys[t_i] = recv_keys[r_i];
      t_i++;
      r_i++;
    }
  }

  memcpy(/* dest */ my_keys, /* src */ temp_keys, local_n * sizeof(int));
}

// local_a中收集较大的值
void merge_high(int local_a[], int temp_b[], int temp_c[], int local_n) {
  int ai, bi, ci;

  ai = local_n - 1;
  bi = local_n - 1;
  ci = local_n - 1;
  while (ci >= 0) {
    if (local_a[ai] >= temp_b[bi]) {
      temp_c[ci] = local_a[ai];
      ci--;
      ai--;
    } else {
      temp_c[ci] = temp_b[bi];
      ci--;
      bi--;
    }
  }

  memcpy(local_a, temp_c, local_n * sizeof(int));
}