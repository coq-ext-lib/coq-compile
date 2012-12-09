#include "data.h"

#include "coqrt.h"

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
  return (rec_len(ptr) != UINTPTR_MAX);
}

char coq_ascii_to_char(universal_t *ptr) {
  assert(rec_len(ptr) == 9);
  unsigned char c = 0;
  /* Coq ascii's are represented lowest significant
     bit first after a constructor... */
  for (int i = 8; i >= 1; i--) {
    c = c << 1;
    c |= (ptr[i] >> 1);
  }
  return (char)c;
}
