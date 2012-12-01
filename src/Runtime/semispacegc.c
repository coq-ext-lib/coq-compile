#include "gc.h"
#include "shadowstack.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <sys/mman.h>

universal_t *tobot, *totop;
universal_t *frombot, *fromtop;
universal_t *curbot, *curtop;
universal_t *queueptr, *endptr;
size_t heapsize;

static void segfault_handler(int sig, siginfo_t *si, void *unused) {
  universal_t *fault = (universal_t *)si->si_addr;
  printf("SIGSEGV at %p\n", fault);
  universal_t *bot, *top;
  if (curbot == frombot) {
    bot = tobot;
    top = totop;
  } else {
    bot = frombot;
    top = fromtop;
  }
  if (bot <= fault && fault < top) {
    printf("Fault in unused space\n");
  }
  exit(-1);
}

void gc_stats(bumpptr_t bumpptrs) {
  size_t remaining = (size_t)bumpptrs.limit - (size_t)bumpptrs.base;
  printf("%lu / %lu bytes allocated\n", heapsize - remaining, heapsize);
}

void dump_heap(bumpptr_t bumpptrs) {
  universal_t *word = curbot;
  printf("Dumping heap from %p to %p\n", word, bumpptrs.base);
  while (word < bumpptrs.base) {
    printf("0x%016lx:\t", (universal_t)word);
    for (uint8_t i = 0; i < 8 && word < bumpptrs.base; i++)
      printf("0x%016lx\t", (universal_t)(*word++));
    printf("\n");
  }
}

bumpptr_t gc_init(size_t capacity) {
  heapsize = capacity;
  frombot =
    (universal_t *)mmap(NULL, heapsize, PROT_READ|PROT_WRITE, MAP_ANON|MAP_PRIVATE, -1, 0);
  if (frombot == (universal_t *)MAP_FAILED) {
    printf("Error: failed to initialize heap.\n");
    exit(-1);
  }
  fromtop = frombot + (heapsize/sizeof(universal_t *));

  tobot =
    (universal_t *)mmap(NULL, heapsize, PROT_READ|PROT_WRITE, MAP_ANON|MAP_PRIVATE, -1, 0);
  if (tobot == (universal_t *)MAP_FAILED) {
    printf("Error: failed to initialize heap.\n");
    exit(-1);
  }
  totop = tobot + (heapsize/sizeof(universal_t *));

  if (debug) {
    printf("Heap initialized with capacity %lu.\n", heapsize);
    printf("fromspace:\t%p\t%p\n", frombot, fromtop);
    printf("tospace:\t%p\t%p\n", tobot, totop);
  }
  curbot = frombot;
  curtop = fromtop;

  /* Protect unused space to detect errors */
  if (debug) {
    if (mprotect((void *)tobot,heapsize,PROT_NONE) != 0) {
      printf("Warning: failed to mprotect unused space\n");
    }

    struct sigaction sa;
    sa.sa_flags = SA_SIGINFO;
    sigemptyset(&sa.sa_mask);
    sa.sa_sigaction = segfault_handler;
    if (sigaction(SIGSEGV, &sa, NULL) == -1) {
      printf("Warning: failed to initialize segfault handler\n");
    }
  }

  return (bumpptr_t) { .base = curbot, .limit = curtop };
}

void forward(universal_t *objref) {
  universal_t *ptr = *((universal_t **)objref);
  if (is_ptr(ptr) && (ptr >= curbot && ptr < curtop)) {
    /* ptr is a pointer into fromspace */
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
      *ptr = (universal_t)endptr + 1;
      *header = 0;
      /* Move the end of the queue forward */
      endptr = j;
    }
    /* ptr must be a forwarding pointer. It either already was, or we 
       forwarded it above. Update the objref to point to the new object */
    *objref = (universal_t)ptr;
  }
}

void visitGCRoot(void **root, const void *meta) {
  forward((universal_t *)root);
}

bumpptr_t coq_gc(void) {
  if (debug) {
    universal_t *tospace = (curbot == tobot) ? frombot : tobot;
    if (mprotect((void *)tospace,heapsize,PROT_READ|PROT_WRITE) != 0) {
      printf("Warning: failed to unprotect unused space\n");
    }
  }

  /* initialize the queue in tospace */
  queueptr = (curtop == fromtop) ? tobot : frombot;
  endptr = queueptr;

  /* Call forward on the roots */
  if (debug)
    printf("Visiting roots...\n");
  visitGCRoots(&visitGCRoot);

  if (debug)
    printf("Running the worklist...\n");
  /* iterate the worklist until we're done copying */
  while (queueptr < endptr) {
    universal_t *objref = queueptr+1;
    assert(is_rec(objref)); /* all heap allocations are records */
    queueptr += rec_len(objref) + 1;
    do {
      forward(objref++);
    } while (objref < queueptr);
  }

  /* Protect the not in use space to detect errors */
  if (debug) {
    if (mprotect((void *)curbot,heapsize,PROT_NONE) != 0) {
      printf("Warning: failed to mprotect unused space\n");
    }
  }

  /* Swap spaces and return the new bump pointers */
  if (curtop == fromtop) {
    curbot = tobot;
    curtop = totop;
  } else {
    curbot = frombot;
    curtop = fromtop;
  }
  assert(curbot <= endptr && endptr < curtop);

  /* allocation starts at the end of the queue */
  return (bumpptr_t) { .base = endptr, .limit = curtop };
}

alloc_t coq_alloc(bumpptr_t bumpptrs, universal_t words) {
  /* TODO: Check for overflow? */
  universal_t *newbase = &bumpptrs.base[words];
  if (newbase > bumpptrs.limit) {
    size_t allocedBefore;
    if (debug) {
      allocedBefore = (universal_t)bumpptrs.base - (universal_t)curbot;
      printf("Starting collection...");
      printf("Bottom: %p Base: %p Limit: %p Top: %p\n", curbot, bumpptrs.base, bumpptrs.limit, curtop);
      assert(allocedBefore <= heapsize);
    }
    bumpptrs = coq_gc();

    assert((universal_t)bumpptrs.limit - heapsize <= (universal_t)bumpptrs.base);

    if (debug) {
      printf(" done.\n");
      printf("Bottom: %p Base: %p Limit: %p\n", curbot, bumpptrs.base, bumpptrs.limit);
      universal_t allocedAfter = (universal_t)bumpptrs.base - (universal_t)curbot;
      printf("Collected %lu / %lu bytes.\n", allocedBefore - allocedAfter, allocedBefore);
    }
    assert(curbot <= bumpptrs.base && bumpptrs.base < bumpptrs.limit);
    /* try again and exit on failure */
    newbase = &bumpptrs.base[words];
    if (newbase > bumpptrs.limit)
      coq_error();
  }

  alloc_t result = {
    .bumpptrs = {
      .base = newbase,
      .limit = bumpptrs.limit
    },
    .ptr = bumpptrs.base
  };
  assert(curbot <= result.ptr && result.ptr < result.bumpptrs.limit
	 && "Invalid allocation result");
  return result;
}
 
