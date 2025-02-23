// 所有线程均输出.
#include <mpi.h>
#include <stdio.h>

int main(void) {
  int comm_sz;  // number of processes
  int my_rank;  // my process rank

  MPI_Init(NULL, NULL);
  MPI_Comm_size(MPI_COMM_WORLD, &comm_sz);
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);

  printf("Proc %d of %d > Does anyone have a toothpick?\n", my_rank, comm_sz);

  MPI_Finalize();
  return 0;
}