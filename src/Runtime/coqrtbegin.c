#include "coqrt.h"
#include "gc.h"

#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define DEFAULTHEAPSIZE 2097152 /* 2MB */

bool debug = false;

bool is_ptr(universal_t *ptr) {
  return ((universal_t)ptr & 0x1) == 0; 
}

universal_t *hdr(universal_t *ptr) {
  return ptr - 1;
}

universal_t rec_len(universal_t *ptr) {
  return *hdr(ptr);
}

bool is_rec(universal_t *ptr) {
  return (rec_len(ptr) != 0);
}

void coq_done(bumpptr_t bumpptrs, universal_t o) {
  if (debug) {
    printf("Program terminated normally.\n");
    printf("Return value: %p\n", (void *)o);
    gc_stats(bumpptrs);
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
  size_t heapsize = DEFAULTHEAPSIZE;

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
  bumpptr_t heap = gc_init(heapsize);

  /* Invoke the Coq program */
  coq_main(heap);
  return 0;
}
