#include "gc.h"
#include "shadowstack.h"
#include "data.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <sys/mman.h>
#include <time.h>

universal_t *tobot, *totop;
universal_t *frombot, *fromtop;
universal_t *curbot, *curtop;
universal_t *queueptr, *endptr;
size_t heapsize;

universal_t allocations;
universal_t allocationsSpace;
universal_t collections;
struct timespec collectionTime;


static void segfault_handler(int sig, siginfo_t *si, void *unused) {
  universal_t *fault = (universal_t *)si->si_addr;
  fprintf(stderr, "SIGSEGV at %p\n", fault);
  universal_t *bot, *top;
  if (curbot == frombot) {
    bot = tobot;
    top = totop;
  } else {
    bot = frombot;
    top = fromtop;
  }
  if (bot <= fault && fault < top) {
    fprintf(stderr, "Fault in unused space\n");
  }

  fprintf(stderr, "Searching backward for header...\n");
  mprotect((void *)bot,heapsize,PROT_READ|PROT_WRITE);
  do {
    fprintf(stderr, "%p:\t0x%016lx\n", fault, *fault);
  } while (!((*fault--) & 0x1));

  exit(-1);
}

void gc_stats(bumpptr_t bumpptrs) {
  double time = (double)collectionTime.tv_sec + (double)collectionTime.tv_nsec/1000000000;

  printf("Garbage collection statistics:\n");
  printf("==============================\n");
  printf("Number of allocations: %lu\n", allocations);
  printf("Total space allocated: %lu bytes\n", allocationsSpace);
  printf("Number of collections: %lu\n", collections);
  printf("Time spent collecting: %0.3f\n", time);
}

void dump_heap(bumpptr_t bumpptrs) {
  universal_t *word = curbot;
  fprintf(stderr, "Dumping heap from %p to %p\n", word, bumpptrs.base);
  while (word < bumpptrs.base) {
    fprintf(stderr, "0x%016lx:\t", (universal_t)word);
    for (uint8_t i = 0; i < 8 && word < bumpptrs.base; i++)
      fprintf(stderr, "0x%016lx\t", (universal_t)(*word++));
    fprintf(stderr, "\n");
  }
}

bumpptr_t gc_init(size_t capacity) {
  heapsize = capacity;
  frombot =
    (universal_t *)mmap(NULL, heapsize, PROT_READ|PROT_WRITE, MAP_ANON|MAP_PRIVATE, -1, 0);
  if (frombot == (universal_t *)MAP_FAILED) {
    fprintf(stderr, "Error: failed to initialize heap.\n");
    exit(-1);
  }
  fromtop = frombot + (heapsize/sizeof(universal_t *));

  tobot =
    (universal_t *)mmap(NULL, heapsize, PROT_READ|PROT_WRITE, MAP_ANON|MAP_PRIVATE, -1, 0);
  if (tobot == (universal_t *)MAP_FAILED) {
    fprintf(stderr, "Error: failed to initialize heap.\n");
    exit(-1);
  }
  totop = tobot + (heapsize/sizeof(universal_t *));

  curbot = frombot;
  curtop = fromtop;

  /* Protect unused space to detect errors */
  if (mprotect((void *)tobot,heapsize,PROT_NONE) != 0)
    fprintf(stderr, "Warning: failed to mprotect unused space\n");

  struct sigaction sa;
  sa.sa_flags = SA_SIGINFO;
  sigemptyset(&sa.sa_mask);
  sa.sa_sigaction = segfault_handler;
  if (sigaction(SIGSEGV, &sa, NULL) == -1) {
    fprintf(stderr, "Warning: failed to initialize segfault handler\n");
  }

  allocations = 0;
  allocationsSpace = 0;
  collections = 0;
  collectionTime.tv_sec = 0;
  collectionTime.tv_nsec = 0;

  return (bumpptr_t) { .base = curbot, .limit = curtop };
}

void forward(universal_t *objref,universal_t offset) {
  universal_t *ptr = *((universal_t **)objref);
  if (is_ptr(ptr) && (ptr >= curbot && ptr < curtop)) {
    /* ptr is a pointer into an object in fromspace */
    /* go to the begining of the object */
    ptr = ptr - offset;
    if (is_rec(ptr)) {
      /* Get a pointer to the header */
      universal_t *header = hdr(ptr);
      /* Retrieve the length of the record (plus one for the header) */
      universal_t len = rec_len(ptr) + 1;
      /* Copy the object starting at the header into tosapce */
      universal_t *i = header;;
      universal_t *j = endptr;
      while (len-- > 0) {
	*j++ = *i++;
      }
      /* Set the forwarding pointer in fromspace and update the record's tag */
      *ptr = (universal_t)(endptr + 1);
      *header = UINTPTR_MAX;
      /* Move the end of the queue forward */
      endptr = j;
    }
    /* ptr must be a forwarding pointer. It either already was, or we 
       forwarded it above. Update the objref to point to the new object */
    *objref = (universal_t)&(*(universal_t **)ptr)[offset] ;
  }
}

void visitGCRoot(void **root, const void *meta) {
  forward((universal_t *)root,(universal_t)meta);
}

bumpptr_t coq_gc(void) {
  struct timespec before;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &before);

  universal_t *tospace = (curbot == tobot) ? frombot : tobot;
  if (mprotect((void *)tospace,heapsize,PROT_READ|PROT_WRITE) != 0)
    fprintf(stderr, "Warning: failed to unprotect unused space\n");

  /* initialize the queue in tospace */
  queueptr = (curbot == frombot) ? tobot : frombot;
  endptr = queueptr;

  /* Call forward on the roots */
  visitGCRoots(&visitGCRoot);

  /* iterate the worklist until we're done copying */
  while (queueptr < endptr) {
    universal_t *objref = queueptr+1;
    assert(is_rec(objref)); /* all heap allocations are records */
    queueptr += rec_len(objref) + 1;
    do {
      forward(objref++,0);
    } while (objref < queueptr);
  }

  /* Protect the not in use space to detect errors */
  if (mprotect((void *)curbot,heapsize,PROT_NONE) != 0) {
    fprintf(stderr, "Warning: failed to mprotect unused space\n");
  }

  /* Swap spaces and return the new bump pointers */
  if (curtop == fromtop) {
    curbot = tobot;
    curtop = totop;
  } else {
    curbot = frombot;
    curtop = fromtop;
  }
  assert(curbot <= endptr && endptr <= curtop);

  /* Statistics */
  struct timespec after;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &after);
  struct timespec diff;
  if ((after.tv_nsec-before.tv_nsec)<0) {
    diff.tv_sec = after.tv_sec-before.tv_sec-1;
    diff.tv_nsec = 1000000000+after.tv_nsec-before.tv_nsec;
  } else {
    diff.tv_sec = after.tv_sec-before.tv_sec;
    diff.tv_nsec = after.tv_nsec-before.tv_nsec;
  }
  collections++;
  collectionTime.tv_sec += diff.tv_sec;
  collectionTime.tv_nsec += diff.tv_nsec;
  if (collectionTime.tv_nsec >= 1000000000) {
    collectionTime.tv_nsec -= 1000000000;
    collectionTime.tv_sec += 1;
  }

  /* allocation starts at the end of the queue */
  return (bumpptr_t) { .base = endptr, .limit = curtop };
}

alloc_t coq_alloc(bumpptr_t bumpptrs, universal_t words) {
  /* TODO: Check for overflow? */
  universal_t *newbase = &bumpptrs.base[words];
  if (newbase > bumpptrs.limit) {
    bumpptrs = coq_gc();
    assert((universal_t)bumpptrs.limit - heapsize <= (universal_t)bumpptrs.base);
    assert(curbot <= bumpptrs.base && bumpptrs.base <= bumpptrs.limit);
    /* try again and exit on failure */
    newbase = &bumpptrs.base[words];
    if (newbase > bumpptrs.limit)
	  coq_error();
  }

  allocations++;
  allocationsSpace += words;

  alloc_t result = {
    .bumpptrs = {
      .base = newbase,
      .limit = bumpptrs.limit
    },
    .ptr = bumpptrs.base
  };
  assert(curbot <= result.ptr);
  assert(curbot <= result.bumpptrs.base);
  assert(result.ptr < result.bumpptrs.limit);
  assert(result.bumpptrs.limit == curtop);
  return result;
}
