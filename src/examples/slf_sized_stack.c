#include "list.h"
#include "list_length.c"

struct sized_stack {
  unsigned int size;
  struct int_list* data;
};

/*@
type_synonym sizeAndData = {u32 s, datatype seq d}

predicate (sizeAndData) SizedStack(pointer p) {
    take S = Owned<struct sized_stack>(p);
    let s = S.size;
    take d = IntList(S.data);
    assert(s == length(d));
    return { s: s, d: d };
}
@*/

extern struct sized_stack *malloc_sized_stack ();
/*@
spec malloc_sized_stack()
     requires true;
     ensures take u = Block<struct sized_stack>(return);
@*/

extern void *free_sized_stack (struct sized_stack *p);
/*@
spec free_sized_stack(pointer p)
     requires take u = Block<struct sized_stack>(p);
     ensures true;
@*/

struct sized_stack* create()
/*@ ensures take S = SizedStack(return);
            S.s == 0u32;
@*/
{
  struct sized_stack *p = malloc_sized_stack();
  p->size = 0;
  p->data = 0;
  /*@ unfold length(Seq_Nil {}); @*/
  return p;
}

unsigned int sizeOf (struct sized_stack *p)
/* FILL IN HERE */
/* ---BEGIN--- */
/*@ requires take S = SizedStack(p);
    ensures take S_ = SizedStack(p);
            S_ == S;
            return == S.s;
@*/
/* ---END--- */
{
  return p->size;
}

void push (struct sized_stack *p, int x)
/* FILL IN HERE */
/* ---BEGIN--- */
/*@ requires take S = SizedStack(p);
    ensures take S_ = SizedStack(p);
            S_.d == Seq_Cons {head:x, tail:S.d};
@*/
/* ---END--- */
{
  struct int_list *data = IntList_cons(x, p->data);
  p->size++;
  p->data = data;
/* ---BEGIN--- */
  /*@ unfold length (Seq_Cons {head: x, tail: S.d}); @*/
/* ---END--- */
}

int pop (struct sized_stack *p)
/* FILL IN HERE */
/* ---BEGIN--- */
/*@ requires take S = SizedStack(p);
             S.s > 0u32;
    ensures  take S_ = SizedStack(p);
             S_.d == tl(S.d);
@*/
/* ---END--- */
{
  struct int_list *data = p->data;
  if (data != 0) {
    int head = data->head;
    struct int_list *tail = data->tail;
    freeIntList(data);
    p->data = tail;
    p->size--;
/* ---BEGIN--- */
    /*@ unfold length(S.d); @*/
/* ---END--- */
    return head;
  }
  return 42;
}

int top (struct sized_stack *p)
/*@ requires take S = SizedStack(p);
             S.s > 0u32;
    ensures  take S_ = SizedStack(p);
             S_ == S;
             return == hd(S.d);
@*/
{
  /*@ unfold length(S.d); @*/ 
  // from S.s > 0u32 it follows that the 'else' branch is impossible
  if (p->data != 0) {
    return (p->data)->head;
  }
  else {
    // provably dead code
    return 42; 
  }
}
