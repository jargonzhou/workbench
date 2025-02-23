#include <string.h>
#include <stdlib.h>
#define MINSIZE(X, Y) (sizeof(X)<sizeof(Y) ? sizeof(X) : sizeof(Y))
#define BYTECOPY(T, S) memcpy(&(T), &(S), MINSIZE(T, S))