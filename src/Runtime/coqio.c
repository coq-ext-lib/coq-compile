#include "io.h"

#include "data.h"
#include <stdio.h>

void coq_printchar(universal_t *ptr) {
  char c = coq_ascii_to_char(ptr);
  fprintf(stderr, "%c", c);
}

