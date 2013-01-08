#include "io.h"

#include "data.h"
#include <stdio.h>

void coq_printchar(universal_t *ptr) {
  char c = coq_ascii_to_char(ptr);
  putc(c, stdout);
}

universal_t coq_fprintchar(bool out, char c) {
  if (out) { 
    return EOF != putc(c, stdout);
  } else {
    return EOF != putc(c, stderr);
  }
}

