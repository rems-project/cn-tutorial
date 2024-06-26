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
datatype dblList {
    dbl_list {datatype seq first, struct Node node, datatype seq rest}
}

datatype emptyList {
    empty_list{}
}

datatype dblListOption {
    Some {datatype dblList l},
    None {datatype emptyList nil}
}

function (struct Node) getNode(datatype dblList l) {
    match l {
        dbl_list {first: f, node: n, rest: r} => {
            n
        }
    }
}


function (datatype seq) flatten(datatype dblList l) {
    match l { 
        dbl_list {first: f, node: n, rest: r} => {
            append(f, Seq_Cons{head: n.data, tail: r})
        }
    }
}

function (datatype seq) flattenOption(datatype dblListOption l) {
    match l { 
        Some {l: l1} => {
            flatten(l1)
        }
        None {nil: n} => {
            Seq_Nil{}
        }
    }
}

function (datatype seq) getFirst(datatype dblList l) {
    match l { 
        dbl_list {first: f, node: n, rest: r} => {
            f
        }
    }
}

function (datatype seq) getRest(datatype dblList l) {
    match l { 
        dbl_list {first: f, node: n, rest: r} => {
            r
        }
    }
}

predicate (datatype dblListOption) LinkedList (pointer p) {
    if (is_null(p)) {
        return None{nil: empty_list{}};
    } else {
        take N = Owned<struct Node>(p);
        take ret = LinkedListHelper(p,N);
        return ret;
    }
}

predicate (datatype dblListOption) LinkedListHelper (pointer p, struct Node N) {
    if (N.next == p && N.prev == p) {
        return None{nil: empty_list{}};
    } else {
        // assert (is_null(N.next) || N.next.prev == N);
        take first = OwnBackwards(N.prev);
        // assert (is_null(N.prev) || N.prev.next == N);
        take rest = OwnForwards(N.next);
        // let nextNode = 
        // return dbl_list{first: first, node: N, rest: rest};
        return Some { l: dbl_list {first: first, node: N, rest: rest} };

    }
}


predicate (datatype seq) OwnForwards(pointer p) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        take rest = OwnForwards(N.next);
        // assert (is_null(N.next) || (*(N.next)).prev == N);
        return Seq_Cons{head: N.data, tail: rest};
    }
}

predicate (datatype seq) OwnBackwards(pointer p) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take N = Owned<struct Node>(p);
        // assert (is_null(N.prev) || N.prev.next == N);
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

struct Node *empty()
/*@ ensures take ret = LinkedList(return);
    flattenOption(ret) == Seq_Nil{};
@*/
{
   struct Node *n = mallocNode();
   n->data = 0;
   n->prev = n;
   n->next = n;
   return n;
}