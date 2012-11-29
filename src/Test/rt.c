#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdint.h>

#define HEAPSIZE 2097152    /* 2MB */
#define UNIVERSAL uintptr_t

struct ret {
  UNIVERSAL *base;
  UNIVERSAL *limit;
  UNIVERSAL val;
};

extern struct ret coq_main(UNIVERSAL *base, UNIVERSAL *limit);

void coq_done(UNIVERSAL *base, UNIVERSAL *limit, UNIVERSAL o) {
  printf("Program terminated normally.\n");
  printf("Return value: %p\n", (void *)o);
  printf("Bytes allocated: %ld\n", HEAPSIZE - (limit - base));
  exit(0);
}

void coq_error() {
  printf("Error: out of memory.\n");
  exit(1);
}

int main() {
  UNIVERSAL *base = (UNIVERSAL *)sbrk((intptr_t)HEAPSIZE);
  if (base == (UNIVERSAL *)-1) {
    printf("Error: failed to initialize heap.\n");
    exit(1);
  }
  UNIVERSAL *limit = (UNIVERSAL *)sbrk(0);
  coq_main(base,limit);
  return *base;
}
