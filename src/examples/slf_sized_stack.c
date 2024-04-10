#include "list.h"

// -----------------------------------------------------------------------
// BCP: Should really #include this from bcp_length.c, not repeat it!
//
// But not sure what's the cleanest way to do that -- need to address
// the multiple include problem...

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
/*@ requires take L1 = IntList(xs)
    ensures take L1_ = IntList(xs);
            L1 == L1_;
            return == length(L1)
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

// -----------------------------------------------------------------------

struct sized_stack {
  unsigned int size;
  struct int_list* data;
};

/*@
datatype sizeAndData {
  SD {u32 s, datatype seq d}
}

predicate (datatype sizeAndData) SizedStack(pointer p) {
    take S = Owned<struct sized_stack>(p);
    let s = S.size;
    take d = IntList(S.data);
    assert(s == length(d));
    return (SD { s: s, d: d });
}
@*/

struct sized_stack* create()
/*@ trusted @*/
// BCP: Is there a less verbose way to write this?
/*@ ensures take S = SizedStack(return);
    match S {
      SD {s:s, d:d} => { s == 0u32 }
    }
@*/
{
  // Call malloc, initialize, etc.
}

unsigned int sizeOf (struct sized_stack *p)
/*@ requires take S = SizedStack(p)
    ensures take S_ = SizedStack(p);
    S_ == S;
    match S {
      SD {s:s, d:d} => { return == s }
    }
@*/
{
  return p->size;
}

struct sized_stack* push (struct sized_stack *p, int x)
/*@ trusted @*/
// BCP: The following is pretty hideous.  Am I doing it wrong?
/*@ requires take S = SizedStack(p)
    ensures take S_ = SizedStack(p);
    match S {
      SD {s:s, d:d} => {
        match S_ {
          SD {s:s_, d:d_} => {
            d_ == Seq_Cons {head:x, tail:d}
          }
        }
      }
    }
@*/
{
  // Once again, I should write the actual code here, but it involves
  // allocation...  I guess I need to just define a malloc and a free
  // for the sized_stack type...
}

// BCP: We could add the pop and top operations...
