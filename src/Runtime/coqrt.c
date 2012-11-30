#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <getopt.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <sys/mman.h>

#define DEFAULTHEAPSIZE 2097152 /* 2MB */
#define UNIVERSAL uintptr_t

struct ret {
  UNIVERSAL *base;
  UNIVERSAL *limit;
  UNIVERSAL val;
};

extern struct ret coq_main(UNIVERSAL *base, UNIVERSAL *limit);

bool debug = false;
size_t heapsize = DEFAULTHEAPSIZE;

void coq_done(UNIVERSAL *base, UNIVERSAL *limit, UNIVERSAL o) {
  if (debug) {
    printf("Program terminated normally.\n");
    printf("Return value: %p\n", (void *)o);
    size_t remaining = (void *)limit - (void *)base;
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
      /* FIXME: possible integer error? */
      heapsize = strtol(optarg, &rest, 0);
      if ((heapsize <= 0) || (strlen(rest) != 1))
	usage(argv[0],-1);

      switch (*rest) {
      case 'k':
      case 'K':
	if (heapsize > (SIZE_MAX/1024)) {
	  printf("Heap size too large.\n");
	  exit(-1);
	}
	heapsize *= 1024;
	break;
      case 'm':
      case 'M':
	if (heapsize > (SIZE_MAX/1048576)) {
	  printf("Heap size too large.\n");
	  exit(-1);
	}
	heapsize *= 1048576;
	break;
      case 'g':
      case 'G':
	if (heapsize > (SIZE_MAX/1073741824)) {
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
  UNIVERSAL *base = (UNIVERSAL *)mmap(NULL, (size_t)heapsize, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE, -1, 0);
  if (base == (UNIVERSAL *)MAP_FAILED) {
    printf("Error: failed to initialize heap.\n");
    exit(-1);
  }
  UNIVERSAL *limit = (UNIVERSAL *)((void *)base + heapsize);

  /* Invoke the Coq program */
  coq_main(base,limit);
  return 0;
}
