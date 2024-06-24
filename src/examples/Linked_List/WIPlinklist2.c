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