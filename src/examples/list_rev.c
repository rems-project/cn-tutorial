#include "list.h"
#include "append.h"

/*@
function [rec] (datatype seq) snoc(datatype seq xs, i32 y) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : h, tail : zs}  => {
      snoc (rev(zs), h)
    }
  }
}

function [rec] (datatype seq) rev(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : h, tail : zs}  => {
      snoc (rev(zs), h)
    }
  }
}

lemma append_nil_r (datatype seq l1)
requires true
ensures append(l1, Seq_Nil {}) == l1

lemma append_nil_l (datatype seq l1)
requires true
ensures append(Seq_Nil {}, l1) == l1

lemma rev_nil ()
requires true
ensures rev(Seq_Nil {}) == Seq_Nil {}

lemma rev_cons (i32 h, datatype seq t)
requires true
ensures rev(Seq_Cons {head: h, tail: t}) == snoc (rev(t), h)

@*/

struct int_list* IntList_rev_aux(struct int_list* xs, struct int_list* ys)
/*@ requires take L1 = IntList(xs) @*/
/*@ requires take L2 = IntList(ys) @*/
/*@ ensures take R = IntList(return) @*/
/*@ ensures R == append(rev(L2), L1) @*/
{
  if (ys == 0) {
    /*@ unfold append(L1,L2); @*/
    /*@ unfold rev(L1); @*/
    /*@ apply append_nil_l(L1); @*/
    /*@ apply rev_nil(); @*/
    return xs;
  } else {
    /*@ unfold append(L1,L2); @*/
    /*@ unfold rev(L1); @*/
    /*@ apply rev_nil(); @*/
    /* BCP: Hmmm -- it seems like maybe I need something like
              apply rev_cons(ys->head, ys->tail);
            but I am not sure how to say it correctly
    */
    struct int_list *tmp = ys->tail;
    ys->tail = xs;
    return IntList_rev_aux(ys, tmp);
  }
}

struct int_list* IntList_rev(struct int_list* xs, int y)
/*@ requires take L1 = IntList(xs) @*/
/*@ ensures take L1_rev = IntList(return) @*/
/*@ ensures L1_rev == rev(L1) @*/
{
  /*@ apply append_nil_r(rev(L1)); @*/
  return IntList_rev_aux (0, xs);
}
