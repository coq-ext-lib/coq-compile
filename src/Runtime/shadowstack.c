#include "shadowstack.h"

/* The head of the singly-linked list of StackEntries. Functions push and 
   pop onto this in their prologue and epilogue.

   Since there is only a global list, this technique is not threadsafe. */
gc_stackentry *llvm_gc_root_chain;

void visitGCRoots(void (*Visitor)(void **Root, const void *Meta)) {
  for (gc_stackentry *R = llvm_gc_root_chain; R; R = R->Next) {
    unsigned i = 0;

    /* For roots [0, NumMeta), the metadata pointer is in the FrameMap. */
    for (unsigned e = R->Map->NumMeta; i != e; ++i)    
	  Visitor(&R->Roots[i], R->Map->Meta[i]);
    
    /* For roots [NumMeta, NumRoots), the metadata pointer is null. */
    for (unsigned e = R->Map->NumRoots; i != e; ++i)
	  Visitor(&R->Roots[i], NULL);
  }
}
