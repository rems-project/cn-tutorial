#include "../list.h"
#include "../list_length.c"
// #include "../list_snoc.h"
#include "../list_append.h"
#include "../list_rev.h"

struct Node {
  int data;  
  struct Node* prev;
  struct Node* next;
};

/*@
datatype dblList {
    FirstRest {datatype dblListOption first, datatype dblListOption rest},
    FirstNodeRest {datatype dblListOption f, struct Node n, datatype dblListOption r}
}

datatype dblListOption {
    empty {},
    nonEmpty {struct Node node, datatype seq tail}
}

function (bool) is_empty(datatype dblListOption l) {
    match l {
        empty{} => {
            true
        }
        nonEmpty{node: n, tail: t} => {
            false
        }
    }
}

function  (struct Node) getNodeOption(dblListOption l) {
    match l {
        empty{} => {
            default<struct Node>
        }
        nonEmpty{node: n2, tail: t} => {
            n2
        }
    }
}

function (struct Node) getNode(dblList l) {
    match l {
        FirstRest{first: f, rest: r} => {
            default<struct Node>
        }
        FirstNodeRest{f: f, n: n, r: r} => {
            n
        }
    }
}

function (datatype dblListOption) getFirst(dblList l) {
    match l {
        FirstRest{first: f, rest: r} => {
            f
        }
        FirstNodeRest{f: f, n: n, r: r} => {
            f
        }
    }
}

function (datatype dblListOption) getRest(dblList l) {
    match l {
        FirstRest{first: f, rest: r} => {
            r
        }
        FirstNodeRest{f: f, n: n, r: r} => {
            r
        }
    }
}

function (datatype seq) flatten(datatype dblList l) {
    match l { 
        FirstRest{ first: f, rest: r} => {
            match f {
                empty{} => { 
                    match r {
                        empty{} => {
                            Seq_Nil{}
                        }
                        nonEmpty{node: n, tail: t} => {
                            Seq_Cons{head: n.data, tail: t}
                        }
                    }
                }
                nonEmpty{node: n, tail: t} => { 
                    match r {
                        empty{} => {
                            rev(Seq_Cons{head: n.data, tail: t})
                        }
                        nonEmpty{node: n2, tail: t2} => {
                            append(rev(Seq_Cons{head: n.data, tail: t}), Seq_Cons{head: n2.data, tail: t2})
                        }
                    }
                }
            }
        }
        FirstNodeRest {f: f, n: n, r: r} => {
            // append(rev(f), Seq_Cons{head: n.data, tail: r})
            match f {
                empty{} => {
                    match r {
                        empty{} => {
                            Seq_Cons{head: n.data, tail: Seq_Nil{}}
                        }
                        nonEmpty{node: n2, tail: t} => {
                            Seq_Cons{head: n.data, tail: Seq_Cons{head: n2.data, tail: t}}
                        }
                    }
                }
                nonEmpty{node: n1, tail: t1} => {
                    match r {
                        empty{} => {
                            rev(Seq_Cons{head: n.data, tail: Seq_Cons{head: n1.data, tail: t1}})
                        }
                        nonEmpty{node: n2, tail: t2} => {
                            append(rev(Seq_Cons{head: n.data, tail: Seq_Cons{head: n1.data, tail: t1}}), Seq_Cons{head: n2.data, tail: t2})
                        }
                    }
                }
            }
        } 
    } 
}

function (datatype seq) flattenOption(dblListOption l) {
    match l {
        empty{} => {
            Seq_Nil{}
        }
        nonEmpty{node: n, tail: t} => {
            Seq_Cons{head: n.data, tail: t}
        }
    }
}

predicate (datatype dblList) LinkedList (pointer p) {
    if (is_null(p)) {
        return FirstRest{first: empty{}, rest: empty{}};
    } else {
        take N = Owned<struct Node>(p);
        take ret = LinkedListAux(p,N);
        return ret;
    }
}

predicate (datatype dblList) LinkedListAux (pointer p, struct Node N) {
    if (ptr_eq(N.next,p) && ptr_eq(N.prev,p)) {
        return FirstRest{first: empty{}, rest: empty{}};
    } else {
        take first = OwnBackwards(N.prev, p, N);
        take rest = OwnForwards(N.next, p, N);
        return FirstNodeRest{f: first, n: N, r: rest};
    }
}

predicate (datatype dblListOption) OwnForwards(pointer p, pointer PrevPointer, struct Node PrevNode) {
    if (is_null(p)) {
        return empty{};
    } else {
        take N = Owned<struct Node>(p);
        assert (ptr_eq(N.prev, PrevPointer));
        assert(ptr_eq(PrevNode.next,p));
        take rest = OwnForwardsAux(N.next, p, N);
        return nonEmpty{node: N, tail: rest};
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



predicate (datatype dblListOption) OwnBackwards(pointer p, pointer NextPointer, struct Node NextNode) {
    if (is_null(p)) {
        return empty{};
    } else {
        take N = Owned<struct Node>(p);
        assert (ptr_eq(N.next,NextPointer));
        assert(ptr_eq(NextNode.prev,p));
        take first = OwnBackwardsAux(N.prev, p, N);
        return nonEmpty{node: N, tail: first};
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

predicate (datatype dblListOption) OwnForwardsAlternate(pointer p) {
    if (is_null(p)) {
        return empty{};
    } else {
        take N = Owned<struct Node>(p);
        take rest = OwnForwardsAux(N.next, p, N);
        return nonEmpty{node: N, tail: rest};
    }
}

predicate (datatype dblListOption) OwnBackwardsAlternate(pointer p) {
    if (is_null(p)) {
        return empty{};
    } else {
        take N = Owned<struct Node>(p);
        take first = OwnBackwardsAux(N.prev, p, N);
        return nonEmpty{node: N, tail: first};
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

struct Node *empty()
/*@ ensures take ret = LinkedList(return);
    ret == FirstRest{first: empty{}, rest: empty{}};
    flatten(ret) == Seq_Nil{};
@*/
{
   struct Node *n = mallocNode();
   n->data = 0;
   n->prev = n;
   n->next = n;
   return n;
}

struct Node *singleton(int element)
/*@ ensures take ret = LinkedList(return);
            flatten(ret) == Seq_Cons{head: element, tail: Seq_Nil{}};
@*/
{
   struct Node *n = mallocNode();
   n->data = element;
   n->prev = 0;
   n->next = 0;
   return n;
}

// is it possible to make the pre and post conditions more concise?
struct Node *add_between_verbose(int element, struct Node *prevNode, struct Node *nextNode)
/*@ requires !is_null(prevNode) && !is_null(nextNode);
             take prev = Owned<struct Node>(prevNode);
             take next = Owned<struct Node>(nextNode);
             take rest = LinkedListAux(nextNode, next);
             take first = LinkedListAux(prevNode, prev);

             ptr_eq(prev.next, nextNode);
             ptr_eq(next.prev, prevNode);

    ensures  take ret = Owned<struct Node>(return);
             take prev_ = Owned<struct Node>(prevNode);
             take next_ = Owned<struct Node>(nextNode);
             take rest_ = LinkedListAux(nextNode, next);
             take first_ = LinkedListAux(prevNode, prev);

             ptr_eq(prev_.next, return);
             ptr_eq(ret.prev, prevNode);
             ptr_eq(ret.next, nextNode);
             ptr_eq(next_.prev, return);
             ptr_eq(prev_.prev, prev.prev);
             ptr_eq(next_.next, next.next);
 
             rest == rest_;
             first == first_;
             //  take l = LinkedListAux(return, ret);
             //  result == append(snoc(first,prev.data), Seq_Cons{head: element, tail: Seq_Cons{head: next.data, tail: rest}});
             //  result != Seq_Nil{};
@*/
{
    struct Node *newNode = mallocNode();

    newNode->prev = prevNode;
    newNode->data = element;
    newNode->next = nextNode;


    prevNode->next = newNode;
    nextNode->prev = newNode;
    // /*@ unfold append(snoc(first,prev.data), Seq_Cons{head: element, tail: Seq_Cons{head: next.data, tail: rest}}); @*/
    return newNode;
}

struct Node *add_between_verbose2(int element, struct Node *prevNode, struct Node *nextNode)
/*@ requires !is_null(prevNode) && !is_null(nextNode);
             take prev = Owned<struct Node>(prevNode);
             take next = Owned<struct Node>(nextNode);
             take l = LinkedListAux(nextNode, next);

             ptr_eq(prev.next, nextNode);
             ptr_eq(next.prev, prevNode);

    ensures  take ret = Owned<struct Node>(return);
             take prev_ = Owned<struct Node>(prevNode);
             take next_ = Owned<struct Node>(nextNode);
             take l_ = LinkedListAux(nextNode, next);

             ptr_eq(prev_.next, return);
             ptr_eq(ret.prev, prevNode);
             ptr_eq(ret.next, nextNode);
             ptr_eq(next_.prev, return);
             ptr_eq(prev_.prev, prev.prev);
             ptr_eq(next_.next, next.next);

            // flatten(l_) != Seq_Nil{};
            // length = length + 1 ??
@*/
{
    struct Node *newNode = mallocNode();

    newNode->prev = prevNode;
    newNode->data = element;
    newNode->next = nextNode;


    prevNode->next = newNode;
    nextNode->prev = newNode;

    return newNode;
}

int remove(struct Node *n)
/*@ requires take del = Owned<struct Node>(n);
             take rest = OwnForwardsAlternate(del.next);
             take first = OwnBackwardsAlternate(del.prev);
             !is_null(del.prev) || !is_null(del.next);
    ensures  take rest_ = OwnForwardsAlternate(del.next);
             take first_ = OwnBackwardsAlternate(del.prev);
             flattenOption(first) == flattenOption(first_);
             flattenOption(rest) == flattenOption(rest_);
             is_empty(first_) ? true : ptr_eq(getNodeOption(first_).next,del.next);
             is_empty(rest_) ? true : ptr_eq(getNodeOption(rest_).prev,del.prev);
@*/ 
{
    if (n->prev == 0) {  // n is the head
        /*@ split_case(is_null((*(*n).next).next)); @*/
        n->next->prev = 0;
    } else if (n->next == 0) { // n is the tail
        /*@ split_case(is_null((*(*n).prev).prev)); @*/
        n->prev->next = 0;
    } else {
        /*@ split_case(is_null((*(*n).prev).prev)); @*/
        /*@ split_case(is_null((*(*n).next).next)); @*/
        struct Node *next = n->next;
        struct Node *prev = n->prev;

        n->next->prev = prev;
        n->prev->next = next;
    }

    int temp = n->data;
    freeNode(n);
    return temp;
}

// void append_dep(int element, struct Node *n)
// /*@ requires !is_null(n);
//              take tailNode = Owned<struct Node>(n);
//              is_null(tailNode.next);
//              take l = LinkedListAux(n, tailNode);
//     ensures  take oldTail = Owned<struct Node>(n);
//              take l_ = LinkedListAux(n, oldTail);
//              !is_null(oldTail.next);
//             //  l_ == dbl_list{first: getFirst(l), rest: snoc(getRest(l), element)};
// @*/
// {
//     /*@ assert(!is_null(n)); @*/
//     /*@ assert(!(ptr_eq((*n).next, n) && ptr_eq((*n).prev, n))); @*/
//     /*@ split_case(ptr_eq((*n).next, n) && ptr_eq((*n).prev, n)); @*/
//     // (ptr_eq(N.next,p) && ptr_eq(N.prev,p)) 
//     struct Node *newNode = mallocNode();
//     newNode->data = element;
//     newNode->prev = n;
//     newNode->next = 0;
//     n->next = newNode;
// }

struct Node* append(int element, struct Node *n)
/*@ requires !is_null(n);
             take tailNode = Owned<struct Node>(n);
             is_null(tailNode.next);
             take l = OwnBackwards(tailNode.prev, n, tailNode);
    ensures  take oldTail = Owned<struct Node>(n);
             take newTail = Owned<struct Node>(return);
             take l_ =  OwnBackwards(tailNode.prev, n, tailNode);
             ptr_eq(oldTail.next, return);
             is_null(newTail.next);
             ptr_eq(newTail.prev, n);
             l_ == l;
@*/
{
    struct Node *newNode = mallocNode();
    newNode->data = element;
    newNode->prev = n;
    newNode->next = 0;
    n->next = newNode;

    return newNode;
}

void append2(int element, struct Node *n)
/*@ requires !is_null(n);
             take tailNode = Owned<struct Node>(n);
             is_null(tailNode.next);
             take l = LinkedListAux(n, tailNode);
    ensures  !is_null(n);
             take oldTail = Owned<struct Node>(n);
             take l_ =  LinkedListAux(n, oldTail);
            //  ptr_eq(oldTail.next, return);
            //  is_null(newTail.next);
            //  ptr_eq(newTail.prev, n);
            //  l_ == l;
@*/
{
    /*@ split_case(ptr_eq((*n).next, n) && ptr_eq((*n).prev, n)); @*/
    struct Node *newNode = mallocNode();
    newNode->data = element;
    newNode->prev = n;
    newNode->next = 0;
    n->next = newNode;

    /*@ assert(ptr_eq((*n).next,newNode)); @*/
    /*@ assert(ptr_eq((*newNode).prev,n)); @*/
    return;
}

void add_helper(int element, struct Node *n)
/*@ requires !is_null(n);
             take node = Owned<struct Node>(n);
             take l = LinkedListAux(n, node);
    ensures  !is_null(n);
             take node_ = Owned<struct Node>(n);
             take l_ = LinkedListAux(n, node_);
@*/
{
    if (n->next == 0) {
        // append(element,n);
    } else {
        // struct Node *newNode = mallocNode();
        // newNode->data = element;
        // newNode->prev = n;
        // newNode->next = n->next;
        // n->next->prev = newNode;
        // n->next = newNode;
        return;
    }
}

void add_WIP(int element, struct Node *n)
/*@ requires !is_null(n);
             take node = Owned<struct Node>(n);
             take l = LinkedListAux(n, node);
    ensures  !is_null(n);
             take node_ = Owned<struct Node>(n);
             take l_ = LinkedListAux(n, node_);
@*/
{
    /*@ split_case(ptr_eq((*n).next, n) && ptr_eq((*n).prev, n)); @*/
    struct Node *next = n->next;
    if (next == n->prev && next == n) { // empty list case
         n->data = element;
         n->prev = 0;
         n->next = 0;
         return;
    } else {
        add_helper(element,n);
        return;
    }
}