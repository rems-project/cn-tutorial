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
    opts {datatype dblListOption first, datatype dblListOption rest},
    seqs {datatype seq f, struct Node n, datatype seq r}
}

datatype dblListOption {
    empty {},
    nonEmpty {struct Node node, datatype seq tail}
}

function (datatype seq) flatten(datatype dblList l) {
    match l { 
        opts{ first: f, rest: r} => {
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
        seqs {f: f, n: n, r: r} => {
            append(rev(f), Seq_Cons{head: n.data, tail: r})
        } 
    } 
}

predicate (datatype dblList) LinkedList (pointer p) {
    if (is_null(p)) {
        return opts{first: empty{}, rest: empty{}};
    } else {
        take N = Owned<struct Node>(p);
        take ret = LinkedListHelper(p,N);
        return ret;
    }
}

predicate (datatype dblList) LinkedListHelper (pointer p, struct Node N) {
    if (ptr_eq(N.next,p) && ptr_eq(N.prev,p)) {
        return opts{first: empty{}, rest: empty{}};
    } else {
        take first = OwnBackwards(N.prev, p, N);
        take rest = OwnForwards(N.next, p, N);
        return opts{first: first, rest: rest};
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
    // ret == dbl_list{first: Seq_Nil{}, rest: Seq_Nil{}};
    flatten(ret) == Seq_Nil{};
@*/
{
   struct Node *n = mallocNode();
   n->data = 0;
   n->prev = n;
   n->next = n;
//    /*@ unfold append(Seq_Nil{}, Seq_Nil{}); @*/
   return n;
}