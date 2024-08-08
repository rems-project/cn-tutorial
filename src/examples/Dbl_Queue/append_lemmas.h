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

void Own_Inner_bwds_append_lemma(struct node *front, struct node *second_front, struct node *last)
/*@
  requires
      take F = Owned<struct node>(front);
      take Second_front = Owned<struct node>(second_front);
      take Last = Owned<struct node>(last);
      take Bwd = Own_Inner_Bwds(Last.prev, last, Last, second_front, Second_front);
      ptr_eq(Second_front.prev, front);
      ptr_eq(F.next, second_front);
  ensures
      take F2 = Owned<struct node>(front);
      take Last2 = Owned<struct node>(last);
      take Bwd2 = Own_Inner_Bwds(Last.prev, last, Last, front, F2);
      Bwd2 == snoc(Bwd, F.data);
      Last == Last2;
      F2 == F;
@*/
{
    /*@ unfold snoc(Seq_Nil{}, front->data); @*/
    /*@ unfold snoc(Bwd, front->data); @*/

    if (last->prev == second_front) {
        return;
    } else {
        Own_Inner_bwds_append_lemma(front, second_front, last->prev);
        return;
    }
}