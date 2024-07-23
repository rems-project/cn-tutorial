#include "./preds_other.c"

void own_forwards_append_lemma(struct node *front, struct node *second_last, struct node *last)
/*@
  requires
      take F = Owned<struct node>(front);
      take Second_last = Owned<struct node>(second_last);
      take Fwd = Own_Forwards(F.next, front, F, second_last, Second_last);
      ptr_eq(Second_last.next, last);
      take Last = Owned<struct node>(last);
      ptr_eq(Last.prev, second_last);
  ensures
      take F2 = Owned<struct node>(front);
      take Last2 = Owned<struct node>(last);
      take Fwd2 = Own_Forwards(F.next, front, F, last, Last2);
      Fwd2 == snoc(Fwd, Second_last.data);
      Last == Last2;
      F2 == F;
@*/
{
    /*@ unfold snoc(Seq_Nil{}, (*second_last).data); @*/
    /*@ unfold snoc(Fwd, (*second_last).data); @*/

    if (front->next == second_last) {
        return;
    } else {
        own_forwards_append_lemma(front->next, second_last, last);
        return;
    }
}

void own_backwards_append_lemma(struct node *front, struct node *second_front, struct node *last)
/*@
  requires
      take F = Owned<struct node>(front);
      take Second_front = Owned<struct node>(second_front);
      take Last = Owned<struct node>(last);
      take Bwd = Own_Backwards(Last.prev, last, Last, second_front, Second_front);
      ptr_eq(Second_front.prev, front);
      ptr_eq(F.next, second_front);
  ensures
      take F2 = Owned<struct node>(front);
      take Last2 = Owned<struct node>(last);
      take Bwd2 = Own_Backwards(Last.prev, last, Last, front, F2);
      Bwd2 == snoc(Bwd, Second_front.data);
      Last == Last2;
      F2 == F;
      ptr_eq(F.next, second_front);
      {front} unchanged; {second_front} unchanged; {last} unchanged;

@*/
{
    /*@ unfold snoc(Seq_Nil{}, (*second_front).data); @*/
    /*@ unfold snoc(Bwd, (*second_front).data); @*/

    if (last->prev == second_front) {
        return;
    } else {
        own_backwards_append_lemma(front, second_front, last->prev);
        return;
    }
}

void own_fwd_eq_bwd_lemma(struct node *front, struct node *back)
/*@ requires
            !ptr_eq(front, back);

            take B = Owned<struct node>(back);
            is_null(B.next);
            !is_null(B.prev);
            
            take F = Owned<struct node>(front);
            !is_null(F.next);

            take Fwd = Own_Forwards(F.next, front, F, back, B);
            ptr_eq(F.next, back) implies Fwd == Seq_Nil{};

            Fwd == Seq_Nil{} implies ptr_eq(F.next, back);
       
    ensures
            take B2 = Owned<struct node>(back);
            B == B2;
            take F2 = Owned<struct node>(front);
            F == F2;
            take Bwd = Own_Backwards(B.prev, back, B, front, F);
            rev(Fwd) == Bwd;
@*/
{
    /*@ unfold rev(Seq_Nil{}); @*/
    if (front->next == 0) {
        return;
    } else {
        if (front->next == back) {
            return;
        } else {
            /*@ split_case(ptr_eq(front->next->next, back)); @*/
            own_fwd_eq_bwd_lemma(front->next, back);
            own_backwards_append_lemma(front, front->next, back);
            /*@ unfold rev(Fwd); @*/
            return;
        }
    }
}

void own_bwd_eq_fwd_lemma(struct node *front, struct node *back)
/*@ requires
            !ptr_eq(front, back);

            take B = Owned<struct node>(back);
            !is_null(B.prev);
            
            take F = Owned<struct node>(front);
            !is_null(F.next);
            is_null(F.prev);

            take Bwd = Own_Backwards(B.prev, back, B, front, F);

            ptr_eq(B.prev, front) implies Bwd == Seq_Nil{};
            Bwd == Seq_Nil{} implies ptr_eq(B.prev, front);
       
    ensures
            take B2 = Owned<struct node>(back);
            B == B2;
            take F2 = Owned<struct node>(front);
            F == F2;
            take Fwd = Own_Forwards(F.next, front, F, back, B);
            rev(Bwd) == Fwd;
@*/
{
    /*@ unfold rev(Seq_Nil{}); @*/
    if (back->prev == 0) {
        return;
    } else {
        if (back->prev == front) {
            return;
        } else {
            /*@ split_case(ptr_eq(back->prev->prev, front)); @*/
            own_bwd_eq_fwd_lemma(front, back->prev);
            own_forwards_append_lemma(front, back->prev, back);
            /*@ unfold rev(Bwd); @*/
            return;
        }
    }
}