#include "list.h"
#include "list_append.h"
#include "list_rev.h"
#include "list_rev_lemmas.h"

struct list_int* rev_loop__list_int(struct list_int *xs)
/*@ requires take L = Linked_List_Int(xs);
    ensures  take L_ = Linked_List_Int(return);
             L_ == Rev__Seq_Int(L);
@*/
{
  struct list_int *last = 0;
  struct list_int *cur = xs;
  /*@ apply Append_Nil_R__Seq_Int(Rev__Seq_Int(L)); @*/
  while(1)
  /*@ inv take L1 = Linked_List_Int(last);
          take L2 = Linked_List_Int(cur);
          Append__Seq_Int(Rev__Seq_Int(L2), L1) == Rev__Seq_Int(L);
  @*/
  {
    if (cur == 0) {
      /*@ unfold Rev__Seq_Int(Nil__Seq_Int{}); @*/
      /*@ unfold Append__Seq_Int(Nil__Seq_Int{}, L1); @*/
      return last;
    }
    struct list_int *tmp = cur->tail;
    cur->tail = last;
    last = cur;
    cur = tmp;
    /*@ unfold Rev__Seq_Int(L2); @*/
    /*@ apply Append_Cons_R__Seq_Int(Rev__Seq_Int(Tl(L2)), Hd(L2), L1); @*/
  }
}
