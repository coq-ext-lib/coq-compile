#ifndef SHADOWSTACK_H
#define SHADOWSTACK_H

#include <stdint.h>
#include <stdio.h>

/* The map for a single function's stack frame. One of these is
   compiled as constant data into the executable for each function.
 
   Storage of metadata values is elided if the %metadata parameter to
   @llvm.gcroot is null. */
typedef struct FrameMap gc_map;
struct FrameMap {
  int32_t NumRoots; /* Number of roots in stack frame. */
  int32_t NumMeta;  /* Number of metadata entries. May be < NumRoots. */
  void *Meta[0];    /* Metadata for each root. */
};

/* A link in the dynamic shadow stack. One of these is embedded in the
   stack frame of each function on the call stack. */
typedef struct StackEntry gc_stackentry;
struct StackEntry {
  gc_stackentry *Next; /* Link to next stack entry (the caller's). */
  gc_map *Map;    /* Pointer to constant FrameMap. */
  void *Roots[0];          /* Stack roots (in-place array). */
};

/* Calls Visitor(root, meta) for each GC root on the stack.
   root and meta are exactly the values passed to @llvm.gcroot.

   Visitor could be a function to recursively mark live objects. Or it
   might copy them to another heap or generation. */
void visitGCRoots(void (*Visitor)(void **Root, const void *Meta));

#endif /* SHADOWSTACK_H */
