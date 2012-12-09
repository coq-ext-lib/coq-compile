#ifndef GC_H
#define GC_H

#import "coqrt.h"

bumpptr_t gc_init(size_t heapsize);
void gc_stats(bumpptr_t bumpptrs);

#endif /* GC_H */
