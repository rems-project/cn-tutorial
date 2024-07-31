#include "list.h"
#include "list_append.h"
#include "list_rev.h"
#include "list_rev_lemmas.h"

struct list_int* rev_aux__list_int(struct list_int* xs, struct list_int* ys)
/*@ requires take L1 = Linked_List_Int(xs); @*/
/*@ requires take L2 = Linked_List_Int(ys); @*/
/*@ ensures take R = Linked_List_Int(return); @*/
/*@ ensures R == Append__Seq_Int(Rev__Seq_Int(L2), L1); @*/
{
  if (ys == 0) {
    /*@ unfold Rev__Seq_Int(L2); @*/
    /*@ unfold Append__Seq_Int(Nil__Seq_Int{}, L1); @*/
    return xs;
  } else {
    /*@ unfold Rev__Seq_Int(L2); @*/
    /*@ apply Append_Cons_R__Seq_Int(Rev__Seq_Int(Tl(L2)), Hd(L2), L1); @*/
    struct list_int *tmp = ys->tail;
    ys->tail = xs;
    return rev_aux__list_int(ys, tmp);
  }
}

struct list_int* rev__list_int(struct list_int* xs)
/*@ requires take L1 = Linked_List_Int(xs); @*/
/*@ ensures take L1_Rev = Linked_List_Int(return); @*/
/*@ ensures L1_Rev == Rev__Seq_Int(L1); @*/
{
  /*@ apply Append_Nil_R__Seq_Int(Rev__Seq_Int(L1)); @*/
  return rev_aux__list_int (0, xs);
}
