#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <getopt.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#define DEFAULTHEAPSIZE 2097152 /* 2MB */
#define UNIVERSAL uintptr_t

struct ret {
  UNIVERSAL *base;
  UNIVERSAL *limit;
  UNIVERSAL val;
};

extern struct ret coq_main(UNIVERSAL *base, UNIVERSAL *limit);

bool debug = false;
intptr_t heapsize = DEFAULTHEAPSIZE;

void coq_done(UNIVERSAL *base, UNIVERSAL *limit, UNIVERSAL o) {
  if (debug) {
    printf("Program terminated normally.\n");
    printf("Return value: %p\n", (void *)o);
    intptr_t remaining = (intptr_t)((void *)limit - (void *)base);
    printf("Bytes allocated: %ld\n", heapsize - remaining);
  }
  exit(0);
}

void coq_error() {
  printf("Error: out of memory.\n");
  exit(-1);
}

void usage(char *program, int exit_code) {
  printf("Usage: %s\n", program);
  printf("\t--debug[=yes/=no], -d      Print debugging information during execution\n");
  printf("\t--Xms=size<k/m/g>          Set the heap size to 'size' KB/MB/GB\n");
  exit(exit_code);
}

int main(int argc, char *argv[]) {
  /* Process command line options */
  while (1) {
    static struct option long_options[] = {
      {"debug", optional_argument, NULL, 'd'},
      {"Xms", required_argument, NULL, 's'},
      {0, 0, 0, 0}
    };

    int option_index = 0;
    int o = getopt_long(argc, argv, "dh", long_options, &option_index);
    char *rest;

    /* Detect the end of options */
    if (o == -1)
      break;
    
    /* Process the current argument */
    switch (o) {
    case 'd':
      if (optarg) {
	if (strcmp("yes",optarg))
	  debug = true;
	else if (strcmp("no",optarg))
	  debug = false;
	else
	  usage(argv[0],-1);
      } else {
	debug = true;
      }
      break;
    case 's':
      heapsize = strtol(optarg, &rest, 0);
      if ((heapsize <= 0) || (strlen(rest) != 1))
	usage(argv[0],-1);

      switch (*rest) {
      case 'k':
      case 'K':
	if (heapsize > (INTPTR_MAX/1024)) {
	  printf("Heap size too large.\n");
	  exit(-1);
	}
	heapsize *= 1024;
	break;
      case 'm':
      case 'M':
	if (heapsize > (INTPTR_MAX/1048576)) {
	  printf("Heap size too large.\n");
	  exit(-1);
	}
	heapsize *= 1048576;
	break;
      case 'g':
      case 'G':
	if (heapsize > (INTPTR_MAX/1073741824)) {
	  printf("Heap size too large.\n");
	  exit(-1);
	}
	heapsize *= 1073741824;
	break;
      default:
	usage(argv[0],-1);
      }
    break;
    case 'h':
      usage(argv[0],0);
    case '?':
    default:
      usage(argv[0],-1);
    }
  }

  /* There should be no further arguments on the command line */
  if (optind < argc)
    usage(argv[0],-1);

  /* Initialize the heap */
  UNIVERSAL *base = (UNIVERSAL *)sbrk((intptr_t)heapsize);
  if (base == (UNIVERSAL *)-1) {
    printf("Error: failed to initialize heap.\n");
    exit(-1);
  }
  UNIVERSAL *limit = (UNIVERSAL *)sbrk(0);
  if (((void *)limit - (void *)base) != heapsize) {
    printf("Error: failed to initialize heap to required size.\n");
    if (debug) {
      printf("Requested: %lu\n", (uintptr_t) heapsize);
      printf("Allocated: %lu\n", (uintptr_t)((void *)limit - (void *)base));
    }
    exit(-1);
  }

  /* Invoke the Coq program */
  coq_main(base,limit);
  return 0;
}
