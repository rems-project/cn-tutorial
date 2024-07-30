// #include "./headers.h"

void Own_Inner_fwds_append_lemma(struct node *front, struct node *second_last, struct node *last)
/*@
  requires
      take F = Owned<struct node>(front);
      take Second_last = Owned<struct node>(second_last);
      take Fwd = Own_Inner_Fwds(F.next, front, F, second_last, Second_last);
      ptr_eq(Second_last.next, last);
      take Last = Owned<struct node>(last);
      ptr_eq(Last.prev, second_last);
  ensures
      take F2 = Owned<struct node>(front);
      take Last2 = Owned<struct node>(last);
      take Fwd2 = Own_Inner_Fwds(F.next, front, F, last, Last2);
      Fwd2 == snoc(Fwd, Last.data);
      Last == Last2;
      F2 == F;
@*/
{
    /*@ unfold snoc(Seq_Nil{}, last->data); @*/
    /*@ unfold snoc(Fwd, last->data); @*/

    if (front->next == second_last) {
        return;
    } else {
        Own_Inner_fwds_append_lemma(front->next, second_last, last);
        return;
    }
}