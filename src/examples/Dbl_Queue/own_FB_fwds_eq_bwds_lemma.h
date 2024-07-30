
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