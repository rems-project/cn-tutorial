#include "list.h"
#include "append.h"
#include "list_rev_spec.h"
#include "list_rev_lemmas.h"

struct int_list* IntList_rev_aux(struct int_list* xs, struct int_list* ys)
/*@ requires take L1 = IntList(xs); @*/
/*@ requires take L2 = IntList(ys); @*/
/*@ ensures take R = IntList(return); @*/
/*@ ensures R == append(rev(L2), L1); @*/
{
  if (ys == 0) {
    /*@ unfold rev(L2); @*/
    /*@ unfold append(Seq_Nil {},L1); @*/
    return xs;
  } else {
    /*@ unfold rev(L2); @*/
    /*@ apply append_cons_r(rev(tl(L2)), hd(L2), L1); @*/
    struct int_list *tmp = ys->tail;
    ys->tail = xs;
    return IntList_rev_aux(ys, tmp);
  }
}

struct int_list* IntList_rev(struct int_list* xs)
/*@ requires take L1 = IntList(xs); @*/
/*@ ensures take L1_rev = IntList(return); @*/
/*@ ensures L1_rev == rev(L1); @*/
{
  /*@ apply append_nil_r(rev(L1)); @*/
  return IntList_rev_aux (0, xs);
}
