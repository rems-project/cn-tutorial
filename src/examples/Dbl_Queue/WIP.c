#include "../list_c_types.h"
#include "../list_cn_types.h"
#include "../list_hdtl.h"
#include "../list_rev.h"

struct dbl_queue {
  struct node* front;  
  struct node* back;
};

struct node {
  int data;  
  struct node* prev;
  struct node* next;
};

/*@

// This predicate owns the outer queue structure and 
// asserts that the front and back pointers are either
// both null or both point to a node. It then takes 
// ownership of the nodes in the list in the forwards
// direction through a call to FB_Forwards. It returns 
// a sequence of integers representing the data in the queue.
predicate (datatype seq) Dbl_Queue_Forwards (pointer l) {
    if (is_null(l)) {
        return Seq_Nil{};
    }
    else {
        take L = Owned<struct dbl_queue>(l);
        assert (   (is_null(L.front)  && is_null(L.back)) 
                || (!is_null(L.front) && !is_null(L.back)));
        take inner = FB_Forwards(L.front, L.back);
        return inner;
    }
}


// This predicate owns the front and back nodes in the queue, and then
// takes calls Own_Forwards to take ownership of the rest of the nodes
// in the queue. It asserts that the front node has a null prev pointer
// and that the back node has a null next pointer. It then returns a
// sequence of integers representing the data in the queue.
predicate (datatype seq) FB_Forwards (pointer front, pointer back) {
    if (is_null(front)) {
        return Seq_Nil{};
    } else {
        if (ptr_eq(front, back)) {
            // Only one node in the list, so only one node to own
            take F = Owned<struct node>(front);
            assert (is_null(F.next));
            assert (is_null(F.prev));
            return Seq_Cons {head: F.data, tail: Seq_Nil{}};
        } else {
            take B = Owned<struct node>(back);
            assert (is_null(B.next));
            take F = Owned<struct node>(front);
            assert(is_null(F.prev));
            take Rest = Own_Forwards(F.next, front, F, back, B.data);
            return Seq_Cons{ head: F.data, tail: Rest};
        }
    }
}

// This recursive predicate takes ownership of a node in the queue, 
// and includes checks that the queue is properly doubly linked. It
// also asserts that any node owned in this predicate is not the front
// or the back node. It calls itself recursively, walking forwards until
// it reaches the last node in the list, which was already owned in the 
// `FB_Forwards` predicate. The base case puts the back node into the sequence,
// in order to avoid a call to `snoc`. This helps avoid future calls to `unfold`.
predicate (datatype seq) Own_Forwards(pointer p, pointer prev_pointer, struct node prev_node, pointer b, i32 b_data) {
    if (ptr_eq(p,b)) {
        return Seq_Cons{head: b_data, tail: Seq_Nil{}};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.prev, prev_pointer));
        assert(ptr_eq(prev_node.next, p));
        assert(!is_null(n.next));
        assert(!is_null(n.prev));
        take Rest = Own_Forwards(n.next, p, n, b, b_data);
        return Seq_Cons{head: n.data, tail: Rest};
    }
}

// This predicate owns the outer queue structure and 
// asserts that the front and back pointers are either
// both null or both point to a node. It then takes 
// ownership of the nodes in the list in the backwards
// direction through a call to FB_Backwards. It returns 
// a sequence of integers representing the data in the queue
// BACKWARDS. It returns the reverse of a call to Dbl_Queue_Forwards.
predicate (datatype seq) Dbl_Queue_Backwards (pointer l) {
    if (is_null(l)) {
        return Seq_Nil{};
    }
    else {
        take L = Owned<struct dbl_queue>(l);
        assert (   (is_null(L.front)  && is_null(L.back)) 
                || (!is_null(L.front) && !is_null(L.back)));
        take inner = FB_Backwards(L.front, L.back);
        return inner;
    }
}

// This predicate owns the front and back nodes in the queue, and then
// takes calls Own_Backwards to take ownership of the rest of the nodes
// in the queue. It asserts that the front node has a null prev pointer
// and that the back node has a null next pointer. It then returns a
// sequence of integers representing the data in the queue BACKWARDS.
predicate (datatype seq) FB_Backwards (pointer front, pointer back) {
    if (is_null(front)) {
        return Seq_Nil{};
    } else {
        if (ptr_eq(front, back)) {
            take B = Owned<struct node>(back);
            assert (is_null(B.next));
            assert (is_null(B.prev));
            return Seq_Cons {head: B.data, tail: Seq_Nil{}};
        } else {
            take B = Owned<struct node>(back);
            assert (is_null(B.next));
            take F = Owned<struct node>(front);
            assert(is_null(F.prev));
            take Rest = Own_Backwards(B.prev, back, B, front, F.data);
            return Seq_Cons{ head: B.data, tail: Rest};
        }
    }
}

// This recursive predicate takes ownership of a node in the queue, 
// and includes checks that the queue is properly doubly linked. It
// also asserts that any node owned in this predicate is not the front
// or the back node. It calls itself recursively, walking backwards until
// it reaches the first node in the list, which was already owned in the 
// `FB_Backwards` predicate. The base case puts the front node into the sequence,
// in order to avoid a call to `snoc`. This helps avoid future calls to `unfold`.
// Note that the front is put in the back because this sequence is backwards.
predicate (datatype seq) Own_Backwards(pointer p, pointer next_pointer, struct node next_node, pointer f, i32 f_data) {
    if (ptr_eq(p,f)) {
        return Seq_Cons{head: f_data, tail: Seq_Nil{}};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.next, next_pointer));
        assert(ptr_eq(next_node.prev, p));
        assert(!is_null(n.next));
        assert(!is_null(n.prev));
        take Rest = Own_Backwards(n.prev, p, n, f, f_data);
        return Seq_Cons{head: n.data, tail: Rest};
    }
}
@*/

extern struct dbl_queue *malloc_dbl_queue();
/*@ spec malloc_dbl_queue();
    requires true;
    ensures take u = Block<struct dbl_queue>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void free_dbl_queue (struct dbl_queue *p);
/*@ spec free_dbl_queue(pointer p);
    requires take u = Block<struct dbl_queue>(p);
    ensures true;
@*/

extern struct node *malloc_node();
/*@ spec malloc_node();
    requires true;
    ensures take u = Block<struct node>(return);
            !is_null(return);
@*/ 

extern void free_node (struct node *p);
/*@ spec free_node(pointer p);
    requires take u = Block<struct node>(p);
    ensures true;
@*/

struct dbl_queue *empty_dbl_queue()
/*@ ensures take ret = Dbl_Queue_Forwards(return);
            ret == Seq_Nil{};
@*/
{
  struct dbl_queue *q = malloc_dbl_queue();
  q->front = 0;
  q->back = 0;
  return q;
}

// Given a dbl queue pointer, inserts a new node
// to the front of the list
void push_front (struct dbl_queue* q, int element)
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Forwards(q);
    ensures  take After = Dbl_Queue_Forwards(q);
             After == Seq_Cons{head: element, tail: Before};
@*/
{
    struct node *new_node = malloc_node();
    new_node->data = element;
    new_node->next = q->front;
    new_node->prev = 0;
    /*@ split_case(ptr_eq((*q).front, (*q).back)); @*/

    if (q->front != 0) {
        /*@ split_case(ptr_eq((*(*q).front).next, (*q).back)); @*/
        q->front->prev = new_node;
        q->front = new_node;

    } else {
        // in this case, the queue is empty
        q->back = new_node;
        q->front = new_node;
    }
}


int pop_front (struct dbl_queue* q)
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Forwards(q);
             Before != Seq_Nil{};
    ensures  take After = Dbl_Queue_Forwards(q);
             After == tl(Before);
             hd(Before) == return;
@*/
{
    if (q->front == 0){
        // impossible case from preconditions
        return 0;
    } else {
    // /*@ split_case is_null((*q).front); @*/
    // /*@ apply empty_queue_seq_nil(q); @*/
    // /*@ assert(Before != Seq_Nil{} implies !is_null((*q).front); @*/
    // /*@ assert(!is_null((*q).front)); @*/
        if (q->front == q->back) { // singleton list case
            int data = q->front->data;
            free_node(q->front);
            q->front = 0;
            q->back = 0;
            return data;

        } else {
            /*@ split_case(ptr_eq((*(*q).front).next, (*q).back)); @*/
            struct node *front = q->front;
            int data = front->data;
            front->next->prev = 0;
            q->front = front->next;
            free_node(front);

            /*@ split_case(ptr_eq((*(*q).front).next, (*q).back)); @*/
            return data;
        }
    }
}

// Given a dbl queue pointer, inserts a new node
// to the back of the list
void push_back (struct dbl_queue* q, int element)
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Backwards(q);
    ensures  take After = Dbl_Queue_Backwards(q);
             After == Seq_Cons{head: element, tail: Before};
            //  Before == snoc(After, element); // reverse???
@*/
{
    struct node *new_node = malloc_node();
    new_node->data = element;
    new_node->next = 0;
    new_node->prev = q->back;
    /*@ split_case(ptr_eq((*q).front, (*q).back)); @*/

    if (q->back != 0) {
        /*@ split_case(ptr_eq((*(*q).back).prev, (*q).front)); @*/
        q->back->next = new_node;
        q->back = new_node;
        return;

    } else {
        // in this case, the queue is empty
        q->back = new_node;
        q->front = new_node;
        return;
    }
}

int pop_back (struct dbl_queue* q)
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Backwards(q);
             Before != Seq_Nil{};
    ensures  take After = Dbl_Queue_Backwards(q);
             After == tl(Before);
             hd(Before) == return;
@*/
{
    if (q->front == 0){
        // impossible case from preconditions
        return 0;
    } else {
        if (q->front == q->back) { // singleton list case
            int data = q->back->data;
            free_node(q->back);
            q->front = 0;
            q->back = 0;
            return data;

        } else {
            /*@ split_case(ptr_eq((*(*q).back).prev, (*q).front)); @*/
            struct node *back = q->back;
            int data = back->data;
            back->prev->next = 0;
            q->back = back->prev;
            free_node(back);

            /*@ split_case(ptr_eq((*(*q).back).prev, (*q).front)); @*/
            return data;
        }
    }
}


void forwards_eq_backwards(struct dbl_queue *q)
/*@
    requires take for1 = Dbl_Queue_Forwards(q);
             take back1 = Dbl_Queue_Backwards(q);
    ensures  take for2 = Dbl_Queue_Forwards(q);
             take back2 = Dbl_Queue_Backwards(q);
             for1 == for2;
             back1 == back2;
             for1 == rev(back1);
             rev(for1) == back1;
@*/
{
    if (q == 0)
    {
        /*@ unfold rev(for1); @*/
        /*@ unfold rev(back1); @*/
        return;
    }
}

// void switch_direction(struct dbl_queue *q)
// /*@
//     requires take forwards = Dbl_Queue_Forwards(q);
//     ensures  take backwards = Dbl_Queue_Backwards(q);
//             //  for1 == for2;
//             //  back1 == back2;
//             //  for1 == rev(back1);
//             //  rev(for1) == back1;
// @*/
// {
//     if (q == 0)
//     {
//         return;
//     } else {
//         if (q->front == 0) {
//             /*@ assert(is_null((*q).back)); @*/
//             return;
//         }
//         else if (q->front == q->back){
//             return;
//         } else {
//             switch_direction();
//             return;
//         }
//     }
// }

// void switch_direction(struct node *front, struct node *back)
// /*@
//     requires take forwards = FB_Forwards(front, back);
//     ensures  take backwards = FB_Backwards(front, back);
//             //  for1 == for2;
//             //  back1 == back2;
//             //  for1 == rev(back1);
//             //  rev(for1) == back1;
// @*/
// {
//     if (front == 0) {
//         return;
//     }
//     else if (front == back){
//         return;
//     } else {
//         /*@ split_case(is_null(front)); @*/
//         /*@ split_case(is_null(back)); @*/
//         /*@ split_case(ptr_eq(front,back)); @*/

//         switch_direction(front->next, back);
//         return;
//     }
// }

void switch_direction(struct node *front, struct node *back)
/*@
    requires take forwards = FB_Forwards(front, back);
    ensures  take backwards = FB_Backwards(front, back);
            //  for1 == for2;
            //  back1 == back2;
            //  for1 == rev(back1);
            //  rev(for1) == back1;
@*/
{
    if (front == 0) {
        return;
    }
    else if (front == back){
        return;
    } else {
        /*@ split_case(is_null(front)); @*/
        /*@ split_case(is_null(back)); @*/
        /*@ split_case(ptr_eq(front,back)); @*/

        switch_direction(front->next, back);
        return;
    }
}

