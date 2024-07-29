#include "./functions.c"
#include "./lemmas.c"

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

void ex_switch1()
{
    struct dbl_queue *q = empty_dbl_queue();
    push_front(q, 1);
    Dbl_Queue_Fwd_At_eq_Bwd_lemma(q);
    /*@ unfold rev(Seq_Cons{ head: 1i32, tail: Seq_Nil{} }); @*/
    /*@ unfold rev(Seq_Nil{}); @*/
    /*@ unfold snoc(Seq_Nil{}, 1i32); @*/
    push_back(q, 2);
    int two = pop_back(q);
    int one = pop_back(q);
    /*@ assert(one == 1i32); @*/
    /*@ assert(two == 2i32); @*/

    /*@ split_case(is_null(q->front)); @*/
    /*@ split_case(ptr_eq(q->front, q->back)); @*/
    free_dbl_queue(q);
}


void ex_switch2()
{
    struct dbl_queue *q = empty_dbl_queue();
    push_front(q, 1);
   
    Dbl_Queue_Fwd_At_eq_Bwd_lemma(q);
    /*@ unfold rev(Seq_Cons{ head: 1i32, tail: Seq_Nil{} }); @*/
    /*@ unfold rev(Seq_Nil{}); @*/
    /*@ unfold snoc(Seq_Nil{}, 1i32); @*/
   
    
    int one = pop_back(q);
    /*@ assert(one == 1i32); @*/

    /*@ split_case(is_null(q->front)); @*/
    /*@ split_case(ptr_eq(q->front, q->back)); @*/
    free_dbl_queue(q);
}

void ex_switch3()
{
    struct dbl_queue *q = empty_dbl_queue();
    push_front(q, 1);
    Dbl_Queue_Fwd_At_eq_Bwd_lemma(q);
    /*@ unfold rev(Seq_Cons{ head: 1i32, tail: Seq_Nil{} }); @*/
    /*@ unfold rev(Seq_Nil{}); @*/
    /*@ unfold snoc(Seq_Nil{}, 1i32); @*/

    push_back(q, 2);
    Dbl_Queue_Bwd_At_eq_Fwd_lemma(q); //rev(2,1) == (1,2)
    /*@ unfold rev(Seq_Cons{ head: 2i32, tail: Seq_Cons{head: 1i32, tail: Seq_Nil{}}}); @*/
    /*@ unfold snoc(Seq_Nil{}, 2i32); @*/
    /*@ unfold snoc(Seq_Cons{head: 1i32, tail: Seq_Nil{}}, 2i32); @*/

    int one = pop_front(q);

    Dbl_Queue_Fwd_At_eq_Bwd_lemma(q);
    /*@ unfold rev(Seq_Cons{ head: 2i32, tail: Seq_Nil{} }); @*/

    int two = pop_back(q);

    /*@ assert(one == 1i32); @*/
    /*@ assert(two == 2i32); @*/

    /*@ split_case(is_null(q->front)); @*/
    /*@ split_case(ptr_eq(q->front, q->back)); @*/
    free_dbl_queue(q);
}