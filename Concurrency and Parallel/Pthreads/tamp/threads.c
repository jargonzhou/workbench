/*
 * threads.c
 *
 * Created on January 2, 2006, 11:43 PM
 *
 * From "Multiprocessor Synchronization and Concurrent Data Structures",
 * by Maurice Herlihy and Nir Shavit.
 * Copyright 2006 Elsevier Inc. All rights reserved.
 */

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

/**
 * Illustrates Pthread creation and joining
 * @author Maurice Herlihy
 */
#define NUM_THREADS 8

void* hello(void* arg) {
  printf("Hello from thread %ld\n", (long)arg);
  return NULL;
}

int main() {
  pthread_t thread[NUM_THREADS];
  int status;
  long i;

  for (i = 0; i < NUM_THREADS; i++) {
    if (pthread_create(&thread[i], NULL, hello, (void*)i) != 0) {
      printf("pthread_create() error");
      exit(-1);
    }
  }
  for (i = 0; i < NUM_THREADS; i++) {
    pthread_join(thread[i], NULL);
  }
}
