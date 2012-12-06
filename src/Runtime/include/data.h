#ifndef DATA_H
#define DATA_H

#include "coqrt.h"

bool is_ptr(universal_t *ptr) __attribute((always_inline));
universal_t *hdr(universal_t *ptr) __attribute((always_inline));
universal_t rec_len(universal_t *ptr) __attribute((always_inline));
bool is_rec(universal_t *ptr) __attribute((always_inline));

char coq_ascii_to_char(universal_t *ptr);

#endif /* DATA_H */
