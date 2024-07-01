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

// function (datatype seq) getFirstOption(dblListOption l) {
//     match l {
//         empty{} => {
//             Seq_Nil{}
//         }
//         nonEmpty{node: n2, tail: t} => {
//             t
//         }
//     }
// }

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

// struct Node *add_between_WIP(int element, struct Node *prevNode, struct Node *nextNode)
// /*@ requires !is_null(prevNode) && !is_null(nextNode);
//              take l = LinkedList(prevNode);
//              let prev = getNode(l);
//              let next = getNodeOption(getRest(l));
             
//              ptr_eq(prev.next, nextNode);
//              ptr_eq(next.prev, prevNode);

//     ensures  take ret = Owned<struct Node>(return);
//              take prev_ = Owned<struct Node>(prevNode);
//              take next_ = Owned<struct Node>(nextNode);
//              take l_ = LinkedListAux(nextNode, next);

//              ptr_eq(prev_.next, return);
//              ptr_eq(ret.prev, prevNode);
//              ptr_eq(ret.next, nextNode);
//              ptr_eq(next_.prev, return);
//              ptr_eq(prev_.prev, prev.prev);
//              ptr_eq(next_.next, next.next);

//             // flatten(l_) != Seq_Nil{};
//             // length = length + 1 ??
// @*/
// {
//     struct Node *newNode = mallocNode();

//     newNode->prev = prevNode;
//     newNode->data = element;
//     newNode->next = nextNode;


//     prevNode->next = newNode;
//     nextNode->prev = newNode;

//     return newNode;
// }

int remove_helper(struct Node *node)
/*@ requires take del = Owned<struct Node>(node);
             !is_null(del.prev) || !is_null(del.next);
             take first = Owned<struct Node>(del.prev);
             take rest = Owned<struct Node>(del.next);   
             take l = LinkedList(del.next);
        
    ensures  take first_ = Owned<struct Node>(del.prev);
             take rest_ = Owned<struct Node>(del.next);   
             take l_ = LinkedList(del.next);
@*/ 
{
    struct Node *prev = node->prev;
    struct Node *next = node->next;

    prev->next = next;
    next->prev = prev;

    int data = node->data;
    freeNode(node);
    return data;
}

int remove(struct Node *n)
/*@ requires take del = Owned<struct Node>(n);
             take first = OwnForwardsAlternate(del.next);
             take rest = OwnBackwardsAlternate(del.prev);
             !is_null(del.prev) || !is_null(del.next);
    ensures  take first_ = OwnForwardsAlternate(del.next);
             take rest_ = OwnBackwardsAlternate(del.prev);
             rest == rest_;
             first == first_;
@*/ 
{
    /*@ split_case(is_null(n)); @*/
    /*@ split_case(is_null((*n).next)); @*/
    /*@ split_case(is_null((*n).prev)); @*/


    if (n->prev == 0) {
        /*@ assert(is_null((*n).prev)); @*/
        /*@ assert(!is_null((*n).next)); @*/

        // n is the head
        // n->next->prev = 0;
    } else if (n->next == 0) {
        /*@ assert(is_null((*n).next)); @*/
        /*@ assert(!is_null((*n).prev)); @*/
        // n is the tail
    //    n->prev->next = 0;
    } else {
        // n->next->prev = 0;
        // n->prev->next = 0;
    }
    int temp = n->data;
    freeNode(n);
    return temp;
}