// TODO - REVIST - no underscored typedef string found

#ifndef CN_UTILS
void *cn_malloc(unsigned long);
void cn_free_sized(void* p, unsigned long s);
#endif

void freeUnsignedInt(unsigned int *p)
/*@ trusted;
  requires take v = Block<int>(p);
  ensures true; @*/
{
    cn_free_sized(p, sizeof(int));
}

struct int_list {
  int head;
  struct int_list* tail;
};

struct int_list *mallocIntList()
/*@ trusted;
    requires true;
    ensures take u = Block<struct int_list>(return);
            !ptr_eq(return, NULL);
@*/
{
    return cn_malloc(sizeof(struct int_list));
}

void freeIntList (struct int_list *p)
/*@ trusted;
    requires take u = Block<struct int_list>(p);
    ensures true;
@*/
{
    cn_free_sized(p, sizeof(struct int_list));
}


/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}

predicate (datatype seq) IntList(pointer p) {
  if (is_null(p)) {
    return Seq_Nil{};
  } else {
    take H = Owned<struct int_list>(p);
    take tl = IntList(H.tail);
    return (Seq_Cons { head: H.head, tail: tl });
  }
}
@*/


/*@
function (i32) hd (datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0i32
    }
    Seq_Cons {head : h, tail : _} => {
      h
    }
  }
}

function (datatype seq) tl (datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : _, tail : tail} => {
      tail
    }
  }
}
@*/


struct int_list* IntList_nil()
/*@ ensures take ret = IntList(return);
            ret == Seq_Nil{};
 @*/
{
  return 0;
}

struct int_list* IntList_cons(int h, struct int_list* t)
/*@ requires take l = IntList(t);
    ensures take ret = IntList(return);
            ret == Seq_Cons{ head: h, tail: l};
 @*/
{
  struct int_list *p = mallocIntList();
  p->head = h;
  p->tail = t;
  return p;
}

// #include "list_length.c"

/* --BEGIN-- */
/*@
function [rec] (u32) length(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0u32
    }
    Seq_Cons {head : h, tail : zs}  => {
      1u32 + length(zs)
    }
  }
}
@*/

/* --END-- */
unsigned int IntList_length (struct int_list *xs)
/* --BEGIN-- */
/*@ requires take L1 = IntList(xs);
    ensures take L1_ = IntList(xs);
            L1 == L1_;
            return == length(L1);
@*/
/* --END-- */
{
  if (xs == 0) {
/* --BEGIN-- */
    /*@ unfold length(L1); @*/
/* --END-- */
    return 0;
  } else {
/* --BEGIN-- */
    /*@ unfold length(L1); @*/
/* --END-- */
    return 1 + IntList_length (xs->tail);
  }
}


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
spec malloc_sized_stack();
     requires true;
     ensures take u = Block<struct sized_stack>(return);
@*/

extern void *free_sized_stack (struct sized_stack *p);
/*@
spec free_sized_stack(pointer p);
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

int main()
/*@ trusted; @*/
{
}
