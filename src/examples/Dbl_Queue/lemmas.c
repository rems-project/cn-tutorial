#include "./predicates.c"

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

void Own_Inner_fwds_eq_bwd_lemma(struct node *front, struct node *back)
/*@ requires
        !ptr_eq(front, back);

        take B = Owned<struct node>(back);
        is_null(B.next);
        !is_null(B.prev);
        
        take F = Owned<struct node>(front);
        !is_null(F.next);

        take Fwd = Own_Inner_Fwds(F.next, front, F, back, B);
    ensures
        take B2 = Owned<struct node>(back);
        B == B2;
        take F2 = Owned<struct node>(front);
        F == F2;
        take Bwd = Own_Inner_Bwds(B.prev, back, B, front, F);
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
                   
                    Own_Inner_fwds_eq_bwd_lemma(front->next, back);
                   
                    Own_Inner_bwds_append_lemma(front, front->next, back);
                    

                    /*@ unfold rev(Seq_Cons{ head: front->data, tail: Fwd}); @*/
                    /*@ unfold snoc(rev(Fwd), front->data); @*/

                
                    return;
                }
            }
        }
    }
}

void Own_Inner_bwds_eq_fwd_lemma(struct node *front, struct node *back)
/*@ requires
            !ptr_eq(front, back);

            take B = Owned<struct node>(back);
            !is_null(B.prev);
            
            take F = Owned<struct node>(front);
            !is_null(F.next);
            is_null(F.prev);

            take Bwd = Own_Inner_Bwds(B.prev, back, B, front, F);
    ensures
            take B2 = Owned<struct node>(back);
            B == B2;
            take F2 = Owned<struct node>(front);
            F == F2;
            take Fwd = Own_Inner_Fwds(F.next, front, F, back, B);
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
                   
                    Own_Inner_bwds_eq_fwd_lemma(front, back->prev);
                   
                    Own_Inner_fwds_append_lemma(front, back->prev, back);
                    

                    /*@ unfold rev(Seq_Cons{ head: back->data, tail: Bwd}); @*/ 
                    /*@ unfold snoc(rev(Bwd), back->data); @*/
                    return;
                }
            }
        }
    }
}

void Own_Front_Back_fwds_eq_bwds_lemma(struct node *front, struct node *back)
/*@ requires
        (is_null(front) && is_null(back)) || (!is_null(front) && !is_null(back));
        take Q_Fwd = Own_Front_Back_Fwds(front, back);
    ensures
        take Q_Bwd = Own_Front_Back_Bwds(front, back);
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
                Own_Inner_fwds_eq_bwd_lemma(front, back);
                return;
            }
        }
    }
}

void Own_Front_Back_bwds_eq_fwds_lemma(struct node *front, struct node *back)
/*@ requires
        (is_null(front) && is_null(back)) || (!is_null(front) && !is_null(back));
        take Q_Bwd = Own_Front_Back_Bwds(front, back);
    ensures
        take Q_Fwd = Own_Front_Back_Fwds(front, back);
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
                Own_Inner_bwds_eq_fwd_lemma(front, back);
                return;
            }
        }
    }
}

void Dbl_Queue_Fwd_At_eq_Bwd_lemma(struct dbl_queue *q)
/*@ requires take Q_Fwd = Dbl_Queue_Fwd_At(q);
    ensures take Q_Bwd = Dbl_Queue_Bwd_At(q);
            rev(Q_Fwd) == Q_Bwd;
            {q} unchanged;
@*/
{
    /*@ unfold rev(Seq_Nil{}); @*/
    if (q == 0) {
        return;
    } else {
        Own_Front_Back_fwds_eq_bwds_lemma(q->front, q->back);
    }
}

void Dbl_Queue_Bwd_At_eq_Fwd_lemma(struct dbl_queue *q)
/*@ requires take Q_Bwd = Dbl_Queue_Bwd_At(q);
    ensures take Q_Fwd = Dbl_Queue_Fwd_At(q);
            rev(Q_Bwd) == Q_Fwd;
            {q} unchanged;
@*/
{
    /*@ unfold rev(Seq_Nil{}); @*/
    if (q == 0) {
        return;
    } else {
        Own_Front_Back_bwds_eq_fwds_lemma(q->front, q->back);
    }
}