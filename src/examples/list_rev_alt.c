#include "list.h"
#include "list_append.h"
#include "list_rev.h"
#include "list_rev_lemmas.h"

struct int_list* IntList_rev_loop(struct int_list *xs)
/*@ requires take L = IntList(xs);
    ensures  take L_ = IntList(return);
             L_ == rev(L);
@*/
{
  struct int_list *last = 0;
  struct int_list *cur = xs;
  /*@ apply append_nil_r(rev(L)); @*/
  while(1)
  /*@ inv take L1 = IntList(last);
          take L2 = IntList(cur);
          append(rev(L2), L1) == rev(L);
  @*/
  {
    if (cur == 0) {
      /*@ unfold rev(Seq_Nil {}); @*/
      /*@ unfold append(Seq_Nil {}, L1); @*/
      return last;
    }
    struct int_list *tmp = cur->tail;
    cur->tail = last;
    last = cur;
    cur = tmp;
    /*@ unfold rev(L2); @*/
    /*@ apply append_cons_r (rev (tl(L2)), hd(L2), L1); @*/
  }
}
