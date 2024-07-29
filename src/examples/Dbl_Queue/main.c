// WIP, currently does not pass

// #include "./predicates.c"
#include "./functions.c"
#include "./lemmas.c"
int main()
{
    struct dbl_queue *q = empty_dbl_queue();
    /*@ assert(!is_null(q)); @*/
    /*@ split_case(is_null(q->front)); @*/
    /*@ split_case(ptr_eq(q->front, q->back)); @*/


    push_front(q, 1);
    // /*@ split_case(is_null(q)); @*/
    // /*@ split_case(is_null(q->front)); @*/
    // /*@ split_case(is_null(q->back)); @*/
    // /*@ split_case(ptr_eq(q->front, q->back)); @*/
    // /*@ assert(ptr_eq(q->front, q->back)); @*/
    // /*@ assert(q->front->data == 1i32); @*/
    // /*@ assert(q->back->data == 1i32); @*/


    // Dbl_Queue_Fwd_At_eq_Bwd_lemma(q);
    // /*@ split_case(is_null(q)); @*/
    // /*@ split_case(is_null(q->front)); @*/
    // /*@ split_case(is_null(q->back)); @*/

    // /*@ split_case(ptr_eq(q->front, q->back)); @*/
    // /*@ assert(ptr_eq(q->front, q->back)); @*/
    // // /*@ assert(q->front->data == 1i32); @*/
    // // /*@ assert(q->back->data == 1i32); @*/


    // push_back(q, 2);
    // /*@ split_case(is_null(q->front)); @*/
    // /*@ split_case(ptr_eq(q->front, q->back)); @*/
    // // /*@ assert(q->front->data == 1i32); @*/
    // // /*@ assert(q->back->data == 2i32); @*/
    // /*@ assert(!ptr_eq(q->front, q->back)); @*/
    // /*@ split_case(ptr_eq(q->back->prev, q->front)); @*/
    // /*@ assert(ptr_eq(q->back->prev, q->front)); @*/
    // // /*@ assert(q->front->data == 1i32); @*/
    // // /*@ assert(q->back->data == 2i32); @*/

    // Dbl_Queue_Bwd_At_eq_Fwd_lemma(q);
    // push_front(q, 3);

   
    // /*@ split_case(is_null(q)); @*/
    // /*@ split_case(is_null(q->front)); @*/ 
    // /*@ split_case(ptr_eq(q->front, q->back)); @*/
    //  /*@ assert(q->front->data == 3i32); @*/
    // // /*@ assert(q->front->next->data == 1i32); @*/
    // /*@ assert(q->back->data == 2i32); @*/

    // /*@ split_case(ptr_eq(q->front->next, q->back)); @*/
    // /*@ split_case(ptr_eq(q->front->next->next, q->back)); @*/
    // /*@ split_case(ptr_eq(q->back->prev, q->front)); @*/

   


    // int three = pop_front(q);


    // /*@ split_case(is_null(q->front)); @*/
    // /*@ split_case(is_null(q->back)); @*/

    // /*@ split_case(ptr_eq(q->front, q->back)); @*/

    // /*@ assert(!is_null(q)); @*/
    // /*@ assert(!is_null(q->front)); @*/
    // /*@ assert(!is_null(q->back)); @*/
    // /*@ assert(q->front->data == 3i32); @*/
    // /*@ assert(q->back->data == 2i32); @*/

    // Dbl_Queue_Fwd_At_eq_Bwd_lemma(q);
    // /*@ split_case(is_null(q)); @*/
    // /*@ split_case(is_null(q->front)); @*/
    // /*@ split_case(is_null(q->back)); @*/

    // /*@ split_case(ptr_eq(q->front, q->back)); @*/

    // /*@ unfold rev(Seq_Nil{}); @*/
    // // /*@ assert(!is_null(q->front)); @*/


    // int two = pop_back(q);
    


    int one = pop_front(q);
    /*@ assert(one == 1i32); @*/
    /*@ split_case(is_null(q->front)); @*/
    /*@ split_case(ptr_eq(q->front, q->back)); @*/
    free_dbl_queue(q);
}

void ex_front()
{
    struct dbl_queue *q = empty_dbl_queue();
    push_front(q, 1);
   
    int one = pop_front(q);
    /*@ assert(one == 1i32); @*/

    /*@ split_case(is_null(q->front)); @*/
    /*@ split_case(ptr_eq(q->front, q->back)); @*/
    free_dbl_queue(q);
}

void ex_back()
{
    struct dbl_queue *q = empty_dbl_queue();

    /*@ split_case(is_null(q->back)); @*/
    /*@ split_case(ptr_eq(q->front, q->back)); @*/

    push_back(q, 1);
   
    int one = pop_back(q);
    /*@ assert(one == 1i32); @*/

    /*@ split_case(is_null(q->front)); @*/
    /*@ split_case(ptr_eq(q->front, q->back)); @*/
   
    free_dbl_queue(q);
}

// void ex_switch()
// {
//     struct dbl_queue *q = empty_dbl_queue();
//     push_front(q, 1);
//     /*@ split_case(is_null(q->front)); @*/
//     /*@ split_case(is_null(q->back)); @*/
//     /*@ split_case(ptr_eq(q->front, q->back)); @*/
//     /*@ split_case(ptr_eq(q->front->next, q->back)); @*/
//     /*@ split_case(is_null(q)); @*/
//     /*@ unfold rev(Seq_Nil{}); @*/
//     /*@ assert(q->front->data == 1i32); @*/
//     /*@ assert(!is_null(q->front)); @*/
//     /*@ assert(!is_null(q->back)); @*/

//     Dbl_Queue_Fwd_At_eq_Bwd_lemma(q);
//     /*@ assert(!is_null(q->front)); @*/
//     /*@ assert(!is_null(q->back)); @*/

//     /*@ assert(q->back->data == 1i32); @*/

//     /*@ unfold rev(Seq_Cons{head: 1i32, tail: Seq_Nil{}}); @*/
//     /*@ unfold rev(Seq_Nil{}); @*/
//     /*@ split_case(is_null(q)); @*/
//     /*@ split_case(is_null(q->front)); @*/
//     /*@ split_case(is_null(q->back)); @*/
//     // /*@ split_case(ptr_eq(q->front, q->back->prev)); @*/


//     /*@ split_case(ptr_eq(q->front, q->back)); @*/
//     int one = pop_back(q);
//     /*@ assert(one == 1i32); @*/

//     /*@ split_case(is_null(q->front)); @*/
//     /*@ split_case(ptr_eq(q->front, q->back)); @*/
//     free_dbl_queue(q);
// }

void ex_switch()
{
    struct dbl_queue *q = empty_dbl_queue();
    push_front(q, 1);
    Dbl_Queue_Fwd_At_eq_Bwd_lemma(q);
    push_back(q, 2);
    int two = pop_back(q);
    int one = pop_back(q);
    /*@ assert(one == 1i32); @*/
    /*@ assert(two == 2i32); @*/

    /*@ split_case(is_null(q->front)); @*/
    /*@ split_case(ptr_eq(q->front, q->back)); @*/
    free_dbl_queue(q);
}


void foo()
{
    struct dbl_queue *q = empty_dbl_queue();
    push_front(q, 1);
   
    Dbl_Queue_Fwd_At_eq_Bwd_lemma(q);
   
    int one = pop_back(q);
    free_dbl_queue(q);
}