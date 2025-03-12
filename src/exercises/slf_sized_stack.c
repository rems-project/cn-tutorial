#include "list/headers.verif.h"
#include "list/length.c"

struct sized_stack
{
  unsigned int size;
  struct sllist *data;
};

/*@
type_synonym SizedStack = {u32 Size, datatype List Data}

predicate (SizedStack) SizedStack_At (pointer p) {
    take P = Owned<struct sized_stack>(p);
    take D = SLList_At(P.data);
    assert(P.size == Length(D));
    return { Size: P.size, Data: D };
}
@*/

extern struct sized_stack *malloc__sized_stack();
/*@
spec malloc__sized_stack();
     requires true;
     ensures take R = Block<struct sized_stack>(return);
@*/

extern void *free__sized_stack(struct sized_stack *s);
/*@
spec free__sized_stack(pointer s);
     requires take R = Block<struct sized_stack>(s);
     ensures true;
@*/

struct sized_stack *create()
/*@ ensures take R = SizedStack_At(return);
            R.Size == 0u32;
@*/
{
  struct sized_stack *s = malloc__sized_stack();
  s->size = 0;
  s->data = 0;
  /*@ unfold Length(Nil {}); @*/
  return s;
}

unsigned int sizeOf(struct sized_stack *s)
/* FILL IN HERE */
/* ---BEGIN--- */
/*@ requires take S = SizedStack_At(s);
    ensures take S_post = SizedStack_At(s);
            S_post == S;
            return == S.Size;
@*/
/* ---END--- */
{
  return s->size;
}

void push(struct sized_stack *s, int x)
/* FILL IN HERE */
/* ---BEGIN--- */
/*@ requires take S = SizedStack_At(s);
    ensures take S_post = SizedStack_At(s);
            S_post.Data == Cons {Head:x, Tail:S.Data};
@*/
/* ---END--- */
{
  struct sllist *data = slcons(x, s->data);
  s->size++;
  s->data = data;
  /* ---BEGIN--- */
  /*@ unfold Length (Cons {Head: x, Tail: S.Data}); @*/
  /* ---END--- */
}

int pop(struct sized_stack *s)
/* FILL IN HERE */
/* ---BEGIN--- */
/*@ requires take S = SizedStack_At(s);
             S.Size > 0u32;
    ensures  take S_post = SizedStack_At(s);
             S_post.Data == Tl(S.Data);
             return == Hd(S.Data);
@*/
/* ---END--- */
{
  struct sllist *data = s->data;
  /* ---BEGIN--- */
  /*@ unfold Length(S.Data); @*/
  // from S.Size > 0u32 it follows that the 'else' branch is impossible
  /* ---END--- */
  if (data != 0)
  {
    int head = data->head;
    struct sllist *tail = data->tail;
    free__sllist(data);
    s->data = tail;
    s->size--;
    return head;
  }
  return 42;
}

int top(struct sized_stack *s)
/*@ requires take S = SizedStack_At(s);
             S.Size > 0u32;
    ensures  take S_post = SizedStack_At(s);
             S_post == S;
             return == Hd(S.Data);
@*/
{
  /*@ unfold Length(S.Data); @*/
  // from S.Size > 0u32 it follows that the 'else' branch is impossible
  if (s->data != 0)
  {
    return (s->data)->head;
  }
  else
  {
    // provably dead code
    return 42;
  }
}
