// Consider an empty list being a null pointer, and have every function return a pointer
// to some part of the list (null pointer if empty list).


#include "../list.h"
// #include "../list_length.c"
// #include "../list_snoc.h"
#include "../list_append.h"
#include "../list_rev.h"
// #include "./pointereq.c"

struct Node {
  int data;  
  struct Node* prev;
  struct Node* next;
};

struct NodeandInt {
  struct Node* node;
  int data;
};

/*@
datatype dll {
    empty_dll {},
    dll {datatype nodeSeq first, struct Node node, datatype nodeSeq rest}
}

datatype nodeSeq {
    nodeSeq_Nil {},
    nodeSeq_Cons {struct Node node, datatype seq tail}
}

function (datatype nodeSeq) dllGetRest(datatype dll l) {
    match l {
        empty_dll {} => { nodeSeq_Nil {} }
        dll {first: _, node: _, rest: r} => { r }
    }
}

function (datatype nodeSeq) dllGetFirst(datatype dll l) {
    match l {
        empty_dll {} => { nodeSeq_Nil {} }
        dll {first: f, node: _, rest: _} => { f }
    }
}

function (struct Node) dllGetNode(datatype dll l) {
    match l {
        empty_dll {} => {  default<struct Node> }
        dll {first: _, node: n, rest: _} => { n }
    }
}

function (struct Node) nodeSeqHead(datatype nodeSeq l) {
    match l {
        nodeSeq_Nil {} => {  default<struct Node> }
        nodeSeq_Cons {node: n, tail: _} => { n }
    }
}

function (datatype seq) nodeSeqTail (datatype nodeSeq l) {
    match l {
        nodeSeq_Nil {} => {  Seq_Nil {} }
        nodeSeq_Cons {node: _, tail: t} => { t }
    }
}

function (datatype seq) flatten(datatype dll l) {
    match l {
        empty_dll {} => { Seq_Nil {} }
        dll {first: f, node: n, rest: r} => { 
            append (rev( Seq_Cons {head: nodeSeqHead(f).data, tail: nodeSeqTail(f)}), 
            Seq_Cons {head: n.data, tail: Seq_Cons { head: nodeSeqHead(r).data, tail: nodeSeqTail(r)}})
        }
    }
}

function (datatype seq) nodeSeqtoSeq(datatype nodeSeq l) {
    match l {
        nodeSeq_Nil {} => { Seq_Nil {} }
        nodeSeq_Cons {node: n, tail: t} => { Seq_Cons {head: n.data, tail: t } }
    }
}


predicate (datatype dll) LinkedList (pointer p) {
    if (is_null(p)) {
        return empty_dll{};
    } else {
        take N = Owned<struct Node>(p);
        take first = OwnBackwards(N.prev, p, N);
        take rest = OwnForwards(N.next, p, N);
        return dll{first: first, node: N, rest: rest};
    }
}

predicate (datatype nodeSeq) OwnForwards(pointer p, pointer PrevPointer, struct Node PrevNode) {
    if (is_null(p)) {
        return nodeSeq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        assert (ptr_eq(N.prev, PrevPointer));
        assert(ptr_eq(PrevNode.next,p));
        take rest = OwnForwardsAux(N.next, p, N);
        return nodeSeq_Cons{node: N, tail: rest};
    }
}

predicate (datatype seq) OwnForwardsAux(pointer p, pointer PrevPointer, struct Node PrevNode) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        assert (ptr_eq(N.prev, PrevPointer));
        assert(ptr_eq(PrevNode.next,p));
        take rest = OwnForwardsAux(N.next, p, N);
        return Seq_Cons{head: N.data, tail: rest};
    }
}



predicate (datatype nodeSeq) OwnBackwards(pointer p, pointer NextPointer, struct Node NextNode) {
    if (is_null(p)) {
        return nodeSeq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        assert (ptr_eq(N.next,NextPointer));
        assert(ptr_eq(NextNode.prev,p));
        take first = OwnBackwardsAux(N.prev, p, N);
        return nodeSeq_Cons{node: N, tail: first};
    }
}

predicate (datatype seq) OwnBackwardsAux(pointer p, pointer NextPointer, struct Node NextNode) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        assert (ptr_eq(N.next,NextPointer));
        assert(ptr_eq(NextNode.prev,p));
        take first = OwnBackwardsAux(N.prev, p, N);
        return Seq_Cons{head: N.data, tail: first};
    }
}

predicate (datatype nodeSeq) OwnForwardsAlternate(pointer p) {
    if (is_null(p)) {
        return nodeSeq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        take rest = OwnForwardsAux(N.next, p, N);
        return nodeSeq_Cons{node: N, tail: rest};
    }
}

predicate (datatype nodeSeq) OwnBackwardsAlternate(pointer p) {
    if (is_null(p)) {
        return nodeSeq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        take first = OwnBackwardsAux(N.prev, p, N);
        return nodeSeq_Cons{node: N, tail: first};
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
        ret == dll{first: nodeSeq_Nil{}, node: struct Node{data: element, prev: NULL, next: NULL}, rest: nodeSeq_Nil{}};
@*/
{
   struct Node *n = mallocNode();
   n->data = element;
   n->prev = 0;
   n->next = 0;
   return n;
}

// Adds after the given node
struct Node *add(int element, struct Node *n)
/*@ requires take l = LinkedList(n);
    ensures  take l_ = LinkedList(return);
@*/
{
    struct Node *newNode = mallocNode();
    newNode->data = element;
    newNode->prev = 0;
    newNode->next = 0;

    if (n == 0) //empty list case
    {
        newNode->prev = 0;
        newNode->next = 0;
        return newNode;
    } else { 
        /*@ split_case(is_null((*n).next)); @*/
        /*@ split_case(is_null((*n).prev)); @*/

       
        newNode->next = n->next;
        newNode->prev = n;

        if (n->next !=0) {
            /*@ split_case(is_null((*(*n).next).next)); @*/
            n->next->prev = newNode;
        }

        n->next = newNode;
        return newNode;
    }
}

// removes the given node from the list and returns another pointer 
// to somewhere in the list, or a null pointer if the list is empty.
// TODO: should also return an int from the deleted node.
struct Node *remove(struct Node *n)
/*@ requires take l = LinkedList(n);
    ensures take l_ = LinkedList(return);
@*/
{
    if (n == 0) { //empty list case
        return n; //null pointer
    } else { 
        struct Node *temp = 0;
        if (n->prev != 0) {
            /*@ split_case(is_null((*(*n).prev).prev)); @*/

            n->prev->next = n->next;
            temp = n->prev;
        }
        if (n->next != 0) {
            /*@ split_case(is_null((*(*n).next).next)); @*/
            n->next->prev = n->prev;
            temp = n->next;
        }

        freeNode(n);
        return temp;
    }
}

// Appends `second` to the end of `first`, where `first` is the tail of the first list and
// `second` is the head of the second list.
struct Node *append (struct Node *first, struct Node *second)
/*@ requires take n1 = Owned<struct Node>(first);
             take n2 = Owned<struct Node>(second);
             take l = OwnBackwards(n1.prev, first, n1);
             take r = OwnForwards(n2.next, second, n2);
             is_null(n1.next) && is_null(n2.prev);
    ensures take n1_ = Owned<struct Node>(first);
            take n2_ = Owned<struct Node>(second);
            take l_ = OwnBackwards(n1.prev, first, n1);
            take r_ = OwnForwards(n2.next, second, n2);
            ptr_eq(n1_.next,second) && ptr_eq(n2_.prev, first);
            l == l_ && r == r_;
@*/
{
    first->next = second;
    second->prev = first;

    return first;
}


