#include "../list.h"
#include "../list_length.c"
#include "../list_snoc.h"
#include "../list_append.h"

struct Node {
  int data;  
  struct Node* prev;
  struct Node* next;
};

/*@ 
predicate (datatype seq) LinkedList (pointer p) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        take first = OwnBackwards(N.prev);
        take rest = OwnForwards(N.next);
        return append(first, Seq_Cons{head: N.data, tail: rest});
    }
}

predicate (datatype seq) OwnForwards(pointer p) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        take rest = OwnForwards(N.next);
        return Seq_Cons{head: N.data, tail: rest};
    }
}

predicate (datatype seq) OwnBackwards(pointer p) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        take first = OwnBackwards(N.prev);
        return snoc(first, N.data);
    }
}
@*/

extern struct Node *mallocNode();
/*@ spec mallocNode();
    requires true;
    ensures take u = Block<struct Node>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void freeNode (struct Node *p);
/*@ spec freeNode(pointer p);
    requires take u = Block<struct Node>(p);
    ensures true;
@*/

struct Node *singleton(int element)
/*@ ensures take ret = LinkedList(return);
            ret == Seq_Cons{head: element, tail: Seq_Nil{}};
@*/
{
   struct Node *n = mallocNode();
   n->data = element;
   n->prev = 0;
   n->next = 0;
   /*@ unfold append(Seq_Nil{}, (Seq_Cons {head: element, tail: Seq_Nil{}})); @*/
   return n;
}

int remove(struct Node *n)
/*@ 
requires take del = Owned<struct Node>(n);
        take rest = OwnForwards(del.next);
        take first = OwnBackwards(del.prev);
        !is_null(del.prev) || !is_null(del.next);
ensures  take rest_ = OwnForwards(del.next);
         take first_ = OwnBackwards(del.prev);
         rest == rest_;
         first == first_;
@*/
{
    if (n->prev == 0) {
        // n is the head
        n->next->prev = 0;
    } else if (n->next == 0) {
        // n is the tail
       n->prev->next = 0;
    } else {
        n->next->prev = 0;
        n->prev->next = 0;
    }
    int temp = n->data;
    freeNode(n);
    return temp;
}

