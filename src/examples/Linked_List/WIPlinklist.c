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

// struct Node *foo() 
// /*@ ensures take ret = Owned<struct Node>(return);
// @*/
// {
//     struct Node *n = mallocNode();
//     n->data = 0;
//     n->prev = 0;
//     n->next = 0;
//     return n;
// }

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