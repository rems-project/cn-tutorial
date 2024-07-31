#include "list.h"
#include "list_append.h"
#include "list_rev.h"
#include "list_rev_lemmas.h"

struct list_int* rev_aux__list_int(struct list_int* l1, struct list_int* l2)
/*@ requires take L1 = Linked_List_Int(l1); @*/
/*@ requires take L2 = Linked_List_Int(l2); @*/
/*@ ensures take R = Linked_List_Int(return); @*/
/*@ ensures R == Append__Seq_Int(Rev__Seq_Int(L2), L1); @*/
{
  if (l2 == 0) {
    /*@ unfold Rev__Seq_Int(L2); @*/
    /*@ unfold Append__Seq_Int(Nil__Seq_Int{}, L1); @*/
    return l1;
  } else {
    /*@ unfold Rev__Seq_Int(L2); @*/
    /*@ apply Append_Cons_R__Seq_Int(Rev__Seq_Int(Tl(L2)), Hd(L2), L1); @*/
    struct list_int *tmp = l2->tail;
    l2->tail = l1;
    return rev_aux__list_int(l2, tmp);
  }
}

struct list_int* rev__list_int(struct list_int* l1)
/*@ requires take L1 = Linked_List_Int(l1); @*/
/*@ ensures take L1_Rev = Linked_List_Int(return); @*/
/*@ ensures L1_Rev == Rev__Seq_Int(L1); @*/
{
  /*@ apply Append_Nil_R__Seq_Int(Rev__Seq_Int(L1)); @*/
  return rev_aux__list_int (0, l1);
}
