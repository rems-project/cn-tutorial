#include <stddef.h>

typedef int VEC_ELEMENT;

struct Vector {
  int size;
  int capacity;
  VEC_ELEMENT *data;
};


void *cn_malloc(size_t size);
void cn_free_sized(void *ptr, size_t size);

/*@

type_synonym VEC_ELEMENT = i32

type_synonym Vec = {
  struct Vector node, 
  map<i32,VEC_ELEMENT> elements
}

predicate (Vec) Vec(pointer p) {
  take node = Owned<struct Vector>(p);
  assert(0i32 <= node.size);
  assert(node.size <= node.capacity);
  let data = node.data;
  take used = each(i32 i; 0i32 <= i && i < node.size) {
    Owned<VEC_ELEMENT>(array_shift<VEC_ELEMENT>(data,i))
  };
  take unused = each(i32 i; node.size <= i && i < node.capacity) {
    Block<VEC_ELEMENT>(array_shift<VEC_ELEMENT>(data,i))
  };
  return { node: node, elements: used };
}


@*/


// Assumes malloc does not fail
struct Vector *vec_empty(int capacity)
/*@
requires
  0i32 <= capacity && capacity <= 100i32;
ensures
  take xs = Vec(return);
  xs.node.size == 0i32;
  xs.node.capacity == capacity;
@*/
{
  struct Vector *p = (struct Vector*) cn_malloc(sizeof(struct Vector));
  p->size = 0;
  p->capacity = capacity;
  p->data = (VEC_ELEMENT*) cn_malloc(sizeof(VEC_ELEMENT) * capacity);
  return p;
}


void vec_free(struct Vector* vec)
/*@
requires
  take xs = Vec(vec);
ensures
  true;
@*/
{
  cn_free_sized(vec->data,sizeof(VEC_ELEMENT) * vec->capacity);
  cn_free_sized(vec, sizeof(struct Vector));
}


VEC_ELEMENT *vec_index(struct Vector const* vec, int i) 
/*@
requires
  take xs = Vec(vec);
  0i32 <= i && i < xs.node.size;
ensures
  take ys = Vec(vec);
  xs == ys;
  array_shift<VEC_ELEMENT>(xs.node.data,i) == return;
@*/
{
  return vec->data + i;
}


void vec_resize(struct Vector *vec, int capacity)
/*@
requires
  take xs = Vec(vec);
  xs.node.size <= capacity;
ensures
  take ys = Vec(vec);
  ys.node.size == xs.node.size;
  ys.node.capacity == capacity;
  xs.elements == ys.elements;
@*/
{
  VEC_ELEMENT *new_data = (VEC_ELEMENT*) cn_malloc(sizeof(VEC_ELEMENT) * capacity);
  size_t i = 0;
  while (i < vec->size) {
    new_data[i] = vec->data[i];
    ++i;
  }
  cn_free_sized(vec->data, sizeof(VEC_ELEMENT) * vec->capacity);
  vec->data = new_data;
  vec->capacity = capacity;
}


void vec_push_back (struct Vector* vec, VEC_ELEMENT el)
/*@
requires
  take xs = Vec(vec);
ensures
  take ys = Vec(vec);
  xs.node.size + 1i32 == ys.node.size;
  xs.elements[xs.node.size: el] == ys.elements; 
@*/
{
  if (vec->size == vec->capacity)
    vec_resize(vec, vec->capacity > 0? 2 * vec->capacity : 1);
  vec->data[vec->size++] = el;
}


void vec_pop_back(struct Vector* vec) 
/*@
requires
  take xs = Vec(vec);
  xs.node.size > 0i32;
ensures
  take ys = Vec(vec);
  ys.node.size + 1i32 == xs.node.size;
  let last = ys.node.size;
  ys.elements[last: xs.elements[last]] == xs.elements;
@*/
{
  size_t new_capacity = vec->capacity >> 1;
  if (--vec->size < new_capacity) vec_resize(vec,new_capacity);
}