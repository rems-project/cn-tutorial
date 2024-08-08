#include "./headers.h"
#include "./append_lemmas.h"

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
