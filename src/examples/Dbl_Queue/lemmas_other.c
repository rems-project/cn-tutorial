#include "./preds_other.c"

//WIP, doesn't verify
// void own_forwards_backwards(struct node *front, struct node *back)
// /*@ requires
//             take B = Owned<struct node>(back);
//             is_null(B.next);
//             take F = Owned<struct node>(front);
//             // ptr_eq(F.next,back) implies ptr_eq(B.prev, front);
//             // ptr_eq(B.prev, front) implies ptr_eq(F.next,back);

//             // (is_null(F.next) && is_null(B.prev)) || (!is_null(F.next) && !is_null(B.prev));

//             // is_null(F.prev); // doesn't work because of recursive call
//             take Fwd = Own_Forwards(F.next, front, F, back, B);
//     ensures
//             take B2 = Owned<struct node>(back);
//             B == B2;
//             take F2 = Owned<struct node>(front);
//             F == F2;
//             take Bwd = Own_Backwards(B.prev, back, B, front, F);
//             Seq_Cons{head: F.data, tail: Fwd} == rev (Seq_Cons{head: B.data, tail: Bwd});
// @*/
// {
//     if (front == 0) {
//         return;
//     } else {
//         if (front == back) {
//             return;
//         } else {
//             /*@ split_case(ptr_eq(front, back)); @*/
//             /*@ split_case(is_null((*front).next)); @*/
//             /*@ unfold rev(Seq_Cons {head: (*front).data, tail: Seq_Nil {}}); @*/
//             /*@ unfold rev(Seq_Nil{}); @*/
//             /*@ unfold snoc(Seq_Nil{}, (*front).data); @*/
//             if (front->next == 0) {
//                 return;
//             } else {
//                 if (front->next == back) {
//                     /*@ split_case(ptr_eq(front, back)); @*/
//                     /*@ split_case(is_null((*front).next)); @*/
//                     /*@ split_case(ptr_eq((*front).next, back)); @*/
//                     /*@ assert(ptr_eq((*back).prev, front)); @*/
//                     return;
//                 } else {
//                     /*@ assert(!is_null((*front).next)); @*/
//                     /*@ assert(!is_null((*(*front).next).next)); @*/
//                     /*@ assert(ptr_eq((*(*front).next).prev, front)); @*/
//                     /*@ assert(!is_null((*back).prev)); @*/
//                     // /*@ assert(!is_null((*(*back).prev).prev)); @*/
//                     own_forwards_backwards(front->next, back);
//                     /*@ assert(!is_null((*front).next)); @*/
//                     /*@ assert(ptr_eq((*(*front).next).prev, front)); @*/

//                     /*@ split_case(ptr_eq(front, back)); @*/
//                     /*@ split_case(is_null((*front).next)); @*/
//                     /*@ split_case(ptr_eq((*front).next, back)); @*/

//                     /*@ split_case(ptr_eq((*(*front).next).next, back)); @*/

//                     /*@ split_case(ptr_eq((*back).prev, front)); @*/

//                     // /*@ split_case(ptr_eq((*(*back).prev).prev, front)); @*/


//                     return;
//                 }
//             }
//         }
//     }
// }

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
