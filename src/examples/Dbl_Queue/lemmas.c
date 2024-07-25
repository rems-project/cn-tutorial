#include "./predicates.c"

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
    ensures
            take B2 = Owned<struct node>(back);
            B == B2;
            take F2 = Owned<struct node>(front);
            F == F2;
            take Bwd = Own_Backwards(B.prev, back, B, front, F);
            rev(Seq_Cons{head: F.data, tail: Fwd}) == Seq_Cons{head: B.data, tail: Bwd};
@*/
{
    if (front == 0) {
        return;
    } else {
        if (front == back) {
            return;
        } else {
            if (front->next == 0) {
                return;
            } else {
                if (front->next == back) {
                    /*@ unfold rev(Seq_Nil{}); @*/
                    /*@ unfold snoc(Seq_Nil{}, front->data); @*/

                    /*@ unfold rev(Seq_Cons{head: back->data, tail: Seq_Nil{}}); @*/
                    /*@ unfold snoc(Seq_Nil{}, back->data); @*/

                    /*@ unfold rev(Seq_Cons{head: front->data, tail: Seq_Cons{head: back->data, tail: Seq_Nil{}}}); @*/

                    /*@ unfold snoc(Seq_Cons{head: back->data, tail: Seq_Nil{}}, front->data); @*/
                    
                    return;
                } else {
                   
                    own_fwd_eq_bwd_lemma(front->next, back);
                   
                    own_backwards_append_lemma(front, front->next, back);
                    

                    /*@ unfold rev(Seq_Cons{ head: front->data, tail: Fwd}); @*/
                    /*@ unfold snoc(rev(Fwd), front->data); @*/

                
                    return;
                }
            }
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
    ensures
            take B2 = Owned<struct node>(back);
            B == B2;
            take F2 = Owned<struct node>(front);
            F == F2;
            take Fwd = Own_Forwards(F.next, front, F, back, B);
            rev(Seq_Cons{head: B.data, tail: Bwd}) == Seq_Cons{head: F.data, tail: Fwd};
@*/
{
    if (back == 0) {
        return;
    } else {
        if (front == back) {
            return;
        } else {
            if (back->prev == 0) {
                return;
            } else {
                if (back->prev == front) {
                    /*@ unfold rev(Seq_Nil{}); @*/
                    /*@ unfold snoc(Seq_Nil{}, back->data); @*/

                    /*@ unfold rev(Seq_Cons{head: front->data, tail: Seq_Nil{}}); @*/ 
                    /*@ unfold snoc(Seq_Nil{}, front->data); @*/

                    /*@ unfold rev(Seq_Cons{head: back->data, tail: Seq_Cons{head: front->data, tail: Seq_Nil{}}}); @*/

                    /*@ unfold snoc(Seq_Cons{head: front->data, tail: Seq_Nil{}}, back->data); @*/
                    
                    return;
                } else {
                   
                    own_bwd_eq_fwd_lemma(front, back->prev);
                   
                    own_forwards_append_lemma(front, back->prev, back);
                    

                    /*@ unfold rev(Seq_Cons{ head: back->data, tail: Bwd}); @*/ 
                    /*@ unfold snoc(rev(Bwd), back->data); @*/
                    return;
                }
            }
        }
    }
}

void FB_Forwards_eq_backwards(struct node *front, struct node *back)
/*@ requires
        (is_null(front) && is_null(back)) || (!is_null(front) && !is_null(back));
        take Q_Fwd = FB_Forwards(front, back);
    ensures
        take Q_Bwd = FB_Backwards(front, back);
        rev(Q_Fwd) == Q_Bwd;
@*/
{
    /*@ unfold rev(Seq_Nil{}); @*/
    if (front == 0) {
        return;
    } else {
        if (front == back) {
            /*@ unfold rev(Seq_Cons{head: back->data, tail: Seq_Nil{}}); @*/
            /*@ unfold snoc(Seq_Nil{}, back->data); @*/
            return;
        } else {
            if (front->next == back)
            {
                /*@ unfold rev(Seq_Cons{head: back->data, tail: Seq_Nil{}}); @*/
                /*@ unfold snoc(Seq_Nil{}, back->data); @*/
                /*@ unfold rev(Q_Fwd); @*/
                /*@ unfold snoc(Seq_Nil{}, front->data); @*/
                /*@ unfold snoc(Seq_Cons{head: back->data, tail: Seq_Nil{}}, front->data); @*/
                    
                return;
            }
            else {
                own_fwd_eq_bwd_lemma(front, back);
                return;
            }
        }
    }
}

void FB_Backwards_eq_Forwards(struct node *front, struct node *back)
/*@ requires
        (is_null(front) && is_null(back)) || (!is_null(front) && !is_null(back));
        take Q_Bwd = FB_Backwards(front, back);
    ensures
        take Q_Fwd = FB_Forwards(front, back);
        rev(Q_Bwd) == Q_Fwd;
@*/
{
    /*@ unfold rev(Seq_Nil{}); @*/
    if (back == 0) {
        return;
    } else {
        if (front == back) {
            /*@ unfold rev(Seq_Cons{head: front->data, tail: Seq_Nil{}}); @*/
            /*@ unfold snoc(Seq_Nil{}, front->data); @*/
            return;
        } else {
            if (back->prev == front)
            {
                /*@ unfold rev(Seq_Cons{head: front->data, tail: Seq_Nil{}}); @*/
                /*@ unfold snoc(Seq_Nil{}, front->data); @*/
                /*@ unfold rev(Q_Bwd); @*/
                /*@ unfold snoc(Seq_Nil{}, back->data); @*/
                /*@ unfold snoc(Seq_Cons{head: front->data, tail: Seq_Nil{}}, back->data); @*/
                    
                return;
            }
            else {
                own_bwd_eq_fwd_lemma(front, back);
                return;
            }
        }
    }
}

void Dbl_Queue_Forwards_eq_backwards(struct dbl_queue *q)
/*@ requires take Q_Fwd = Dbl_Queue_Forwards(q);
    ensures take Q_Bwd = Dbl_Queue_Backwards(q);
            rev(Q_Fwd) == Q_Bwd;
@*/
{
    /*@ unfold rev(Seq_Nil{}); @*/
    if (q == 0) {
        return;
    } else {
        FB_Forwards_eq_backwards(q->front, q->back);
    }
}

void Dbl_Queue_Backwards_eq_Forwards(struct dbl_queue *q)
/*@ requires take Q_Bwd = Dbl_Queue_Backwards(q);
    ensures take Q_Fwd = Dbl_Queue_Forwards(q);
            rev(Q_Bwd) == Q_Fwd;
@*/
{
    /*@ unfold rev(Seq_Nil{}); @*/
    if (q == 0) {
        return;
    } else {
        FB_Backwards_eq_Forwards(q->front, q->back);
    }
}