// MPI Hello World.
// 非0的线程发送消息到线程0, 线程0输出这些消息.
#include <mpi.h>
#include <stdio.h>
#include <string.h>

const int MAX_STRING = 100;

int main(void) {
  char greeting[MAX_STRING];
  int comm_sz;  // number of processes
  int my_rank;  // my process rank

  // setup
  MPI_Init(NULL, NULL);
  // communicator: MPI_COMM_WORLD
  // get its information: number of processes, the calling process's rank
  MPI_Comm_size(MPI_COMM_WORLD, &comm_sz);
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);

  if (my_rank != 0) {
    sprintf(greeting, "Greetings from process %d of %d!", my_rank, comm_sz);
    MPI_Send(greeting, strlen(greeting) + 1,  // message buffer and size
             MPI_CHAR,                        // message type
             0,                               // dest
             0,                               // tag
             MPI_COMM_WORLD                   // communicator
    );
  } else {
    printf("Greetings from process %d of %d!\n", my_rank, comm_sz);
    for (int q = 1; q < comm_sz; q++) {
      MPI_Recv(greeting, MAX_STRING,  // message buffer and size
               MPI_CHAR,              // message type
               q,                     // source: special value MPI_ANY_SOURCE
               0,                     // tag: special value MPI_ANY_TAG
               MPI_COMM_WORLD,        // communicator
               MPI_STATUS_IGNORE      // MPI_Status struct: MPI_SOURCE, MPI_TAG,
                                      //                    MPI_ERROR
      );
      // use MPI_Get_count(&status, ...) to get the number of elements received
      printf("%s\n", greeting);
    }
  }

  // clean up
  MPI_Finalize();
  return 0;
}