#include "vector.h"
#include "string.h"
#include "stdlib.h"


// Assumes malloc does not fail
Vector *vec_empty(size_t capacity) {
  Vector *p = (Vector*) malloc(sizeof(Vector));
  p->size = 0;
  p->capacity = capacity;
  p->data = (VEC_ELEMENT*) malloc(sizeof(VEC_ELEMENT[capacity]));
  return p;
}

// capacity >= size
void vec_resize(Vector *vec, size_t capacity) {
  VEC_ELEMENT *new_data = (VEC_ELEMENT*) malloc(sizeof(VEC_ELEMENT[capacity]));
  memcpy(new_data, vec->data, sizeof(VEC_ELEMENT[vec->size]));
  free(vec->data);
  vec->data = new_data;
  vec->capacity = capacity;
}

// Assumes malloc does not fail
void vec_push_back(Vector* vec, VEC_ELEMENT el) {
  if (vec->size == vec->capacity)
    vec_resize(vec, vec->capacity > 0? 2 * vec->capacity : 1);
  vec->data[vec->size++] = el;
}

// i < size
VEC_ELEMENT *vec_index(Vector const* vec, size_t i) {
  return vec->data + i;
}

// size > 0
void vec_pop_back(Vector* vec) {
  size_t new_capacity = vec->capacity >> 1;
  if (--vec->size < new_capacity) vec_resize(vec,new_capacity);
}

void vec_free(Vector* vec) {
  free(vec->data);
  free(vec);
}
