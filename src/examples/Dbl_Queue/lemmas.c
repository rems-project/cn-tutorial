#include "./WIP.c"

void own_forwards_backwards(struct node *front, struct node *back)
/*@ requires
            take B = Owned<struct node>(back);
            is_null(B.next);
            take F = Owned<struct node>(front);
            // ptr_eq(F.next,back) implies ptr_eq(B.prev, front);
            // ptr_eq(B.prev, front) implies ptr_eq(F.next,back);

            // (is_null(F.next) && is_null(B.prev)) || (!is_null(F.next) && !is_null(B.prev));

            // is_null(F.prev); // doesn't work because of recursive call
            take Fwd = Own_Forwards(F.next, front, F, back, B);
    ensures
            take B2 = Owned<struct node>(back);
            B == B2;
            take F2 = Owned<struct node>(front);
            F == F2;
            take Bwd = Own_Backwards(B.prev, back, B, front, F);
            Seq_Cons{head: F.data, tail: Fwd} == rev (Seq_Cons{head: B.data, tail: Bwd});
@*/
{
    if (front == 0) {
        return;
    } else {
        if (front == back) {
            return;
        } else {
            /*@ split_case(ptr_eq(front, back)); @*/
            /*@ split_case(is_null((*front).next)); @*/
            /*@ unfold rev(Seq_Cons {head: (*front).data, tail: Seq_Nil {}}); @*/
            /*@ unfold rev(Seq_Nil{}); @*/
            /*@ unfold snoc(Seq_Nil{}, (*front).data); @*/
            if (front->next == 0) {
                return;
            } else {
                if (front->next == back) {
                    /*@ split_case(ptr_eq(front, back)); @*/
                    /*@ split_case(is_null((*front).next)); @*/
                    /*@ split_case(ptr_eq((*front).next, back)); @*/
                    /*@ assert(ptr_eq((*back).prev, front)); @*/
                    return;
                } else {
                    /*@ assert(!is_null((*front).next)); @*/
                    /*@ assert(!is_null((*(*front).next).next)); @*/
                    /*@ assert(ptr_eq((*(*front).next).prev, front)); @*/
                    /*@ assert(!is_null((*back).prev)); @*/
                    // /*@ assert(!is_null((*(*back).prev).prev)); @*/
                    own_forwards_backwards(front->next, back);
                    /*@ assert(!is_null((*front).next)); @*/
                    /*@ assert(ptr_eq((*(*front).next).prev, front)); @*/

                    /*@ split_case(ptr_eq(front, back)); @*/
                    /*@ split_case(is_null((*front).next)); @*/
                    /*@ split_case(ptr_eq((*front).next, back)); @*/

                    /*@ split_case(ptr_eq((*(*front).next).next, back)); @*/

                    /*@ split_case(ptr_eq((*back).prev, front)); @*/

                    // /*@ split_case(ptr_eq((*(*back).prev).prev, front)); @*/


                    return;
                }
            }
        }
    }
}