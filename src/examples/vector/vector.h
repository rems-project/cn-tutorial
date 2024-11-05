#ifndef VECTOR_H
#define VECTOR_H

#include <stddef.h>

typedef int VEC_ELEMENT;

typedef struct {
  size_t size;
  size_t capacity;
  VEC_ELEMENT *data;
} Vector;

Vector *vec_empty();
VEC_ELEMENT *vec_index(Vector const *vec, size_t index);
void vec_push_back(Vector *vec, VEC_ELEMENT el);
void vec_pop_back(Vector *vec);
void vec_free(Vector *vec);
#endif
