#include "../list.h"
#include "../list_append.h"
#include "../list_rev.h"

struct node {
  int data;  
  struct node* prev;
  struct node* next;
};

struct node_and_int {
  struct node* node;
  int data;
};

/*@
datatype Dll {
    Empty_Dll {},
    Dll {datatype Seq_Node first, struct node n, datatype Seq_Node rest}
}

datatype Seq_Node {
    Seq_Node_Nil {},
    Seq_Node_Cons {struct node n, datatype seq tail}
}

function (datatype Seq_Node) Dll_Rest (datatype Dll L) {
    match L {
        Empty_Dll {} => { Seq_Node_Nil {} }
        Dll {first: _, n: _, rest: r} => { r }
    }
}

function (datatype Seq_Node) Dll_First(datatype Dll L) {
    match L {
        Empty_Dll {} => { Seq_Node_Nil {} }
        Dll {first: f, n: _, rest: _} => { f }
    }
}

function (struct node) Dll_Node (datatype Dll L) {
    match L {
        Empty_Dll {} => {  default<struct node> }
        Dll {first: _, n: n, rest: _} => { n }
    }
}

function (struct node) Seq_Node_Head(datatype Seq_Node S) {
    match S {
        Seq_Node_Nil {} => {  default<struct node> }
        Seq_Node_Cons {n: n, tail: _} => { n }
    }
}

function (datatype seq) Seq_Node_Tail (datatype Seq_Node S) {
    match S {
        Seq_Node_Nil {} => {  Seq_Nil {} }
        Seq_Node_Cons {n: _, tail: t} => { t }
    }
}

function (datatype seq) flatten (datatype Dll L) {
    match L {
        Empty_Dll {} => { Seq_Nil {} }
        Dll {first: f, n: n, rest: r} => { 
            match f {
                Seq_Node_Nil {} => {
                    match r {
                        Seq_Node_Nil {} => { 
                            Seq_Cons {head: n.data, tail: Seq_Nil {}} 
                        }
                        Seq_Node_Cons {n: nextNode, tail: t} => {  
                            Seq_Cons {head: n.data, tail: Seq_Cons{ head: nextNode.data, tail: t}}
                        }
                    }
                }
                Seq_Node_Cons {n: prevNode, tail: t} => { 
                    match r {
                        Seq_Node_Nil {} => { 
                            rev(Seq_Cons {head: n.data, tail: Seq_Cons {head: prevNode.data, tail: t}})
                        }
                        Seq_Node_Cons {n: nextNode, tail: t2} => {  
                            append(rev(Seq_Cons {head: prevNode.data, tail: t2}), Seq_Cons {head: n.data, tail: Seq_Cons{ head: nextNode.data, tail: t2}})
                        }
                    }
                }
            }
        }
    }
}

function (datatype seq) Seq_Node_to_Seq(datatype Seq_Node L) {
    match L {
        Seq_Node_Nil {} => { Seq_Nil {} }
        Seq_Node_Cons {n: n, tail: t} => { Seq_Cons {head: n.data, tail: t } }
    }
}


predicate (datatype Dll) LinkedList (pointer p) {
    if (is_null(p)) {
        return Empty_Dll{};
    } else {
        take n = Owned<struct node>(p);
        take First = Own_Backwards(n.prev, p, n);
        take Rest = Own_Forwards(n.next, p, n);
        return Dll{first: First, n: n, rest: Rest};
    }
}

predicate (datatype Seq_Node) Own_Forwards(pointer p, pointer prev_pointer, struct node prev_node) {
    if (is_null(p)) {
        return Seq_Node_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.prev, prev_pointer));
        assert(ptr_eq(prev_node.next,p));
        take Rest = Own_Forwards_Aux(n.next, p, n);
        return Seq_Node_Cons{n: n, tail: Rest};
    }
}

predicate (datatype seq) Own_Forwards_Aux(pointer p, pointer prev_pointer, struct node prev_node) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.prev, prev_pointer));
        assert(ptr_eq(prev_node.next, p));
        take Rest = Own_Forwards_Aux(n.next, p, n);
        return Seq_Cons{head: n.data, tail: Rest};
    }
}



predicate (datatype Seq_Node) Own_Backwards(pointer p, pointer next_pointer, struct node next_node) {
    if (is_null(p)) {
        return Seq_Node_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.next, next_pointer));
        assert(ptr_eq(next_node.prev, p));
        take First = Own_Backwards_Aux(n.prev, p, n);
        return Seq_Node_Cons{n: n, tail: First};
    }
}

predicate (datatype seq) Own_Backwards_Aux(pointer p, pointer next_pointer, struct node next_node) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.next, next_pointer));
        assert(ptr_eq(next_node.prev, p));
        take First = Own_Backwards_Aux(n.prev, p, n);
        return Seq_Cons{head: n.data, tail: First};
    }
}
@*/

extern struct node *malloc_node();
/*@ spec malloc_node();
    requires true;
    ensures take u = Block<struct node>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void free_node (struct node *p);
/*@ spec free_node(pointer p);
    requires take u = Block<struct node>(p);
    ensures true;
@*/

extern struct node_and_int *malloc_node_and_int();
/*@ spec malloc_node_and_int();
    requires true;
    ensures take u = Block<struct node_and_int>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void free_node_and_int (struct node_and_int *p);
/*@ spec free_node_and_int(pointer p);
    requires take u = Block<struct node_and_int>(p);
    ensures true;
@*/

struct node *singleton(int element)
/*@ ensures take Ret = LinkedList(return);
        Ret == Dll{first: Seq_Node_Nil{}, n: struct node{data: element, prev: NULL, next: NULL}, rest: Seq_Node_Nil{}};
@*/
{
   struct node *n = malloc_node();
   n->data = element;
   n->prev = 0;
   n->next = 0;
   return n;
}

// Adds after the given node
// TODO: fix correctness checks
struct node *add(int element, struct node *n)
/*@ requires take L = LinkedList(n);
             let node = Dll_Node(L);
             let First = Dll_First(L);
             let Rest = Dll_Rest(L);
    ensures  take L_ = LinkedList(return);
             let First_ = Dll_First(L_);
             let Rest_ = Dll_Rest(L_);
             let new_node = Dll_Node(L_);

             ptr_eq(new_node.prev, n);
             let node_ = Seq_Node_Head(First_);
             !is_null(n) implies ptr_eq(node_.next, return);
             !is_null(n) implies ptr_eq(new_node.next, node.next);
             !is_null(return);


             !is_null(n) implies Seq_Node_to_Seq(First_) == Seq_Cons { head: node.data, tail: Seq_Node_to_Seq(First)}; 
             Seq_Node_to_Seq(Rest) == Seq_Node_to_Seq(Rest_);
@*/
{
    struct node *new_node = malloc_node();
    new_node->data = element;
    new_node->prev = 0;
    new_node->next = 0;

    if (n == 0) //empty list case
    {
        new_node->prev = 0;
        new_node->next = 0;
        return new_node;
    } else { 
        /*@ split_case(is_null((*n).next)); @*/
        /*@ split_case(is_null((*n).prev)); @*/

       
        new_node->next = n->next;
        new_node->prev = n;

        if (n->next !=0) {
            /*@ split_case(is_null((*(*n).next).next)); @*/
            n->next->prev = new_node;
        }

        n->next = new_node;
        return new_node;
    }
}


// Appends `second` to the end of `first`, where `first` is the tail of the first list and
// `second` is the head of the second list.
// TODO: fix so that any nodes can be passed in, not just head and tail
struct node *append (struct node *first, struct node *second)
/*@ requires take n1 = Owned<struct node>(first);
             take n2 = Owned<struct node>(second);
             take L = Own_Backwards(n1.prev, first, n1);
             take R = Own_Forwards(n2.next, second, n2);
             is_null(n1.next) && is_null(n2.prev);
    ensures take n1_ = Owned<struct node>(first);
            take n2_ = Owned<struct node>(second);
            take L_ = Own_Backwards(n1.prev, first, n1);
            take R_ = Own_Forwards(n2.next, second, n2);
            ptr_eq(n1_.next,second) && ptr_eq(n2_.prev, first);
            L == L_ && R == R_;
@*/
{
    first->next = second;
    second->prev = first;

    return first;
}

// removes the given node from the list and returns another pointer 
// to somewhere in the list, or a null pointer if the list is empty.
struct node_and_int *remove(struct node *n)
/*@ requires !is_null(n);
             take del = Owned<struct node>(n);
             take First = Own_Backwards(del.prev, n, del);
             take Rest = Own_Forwards(del.next, n, del);
    ensures  take ret = Owned<struct node_and_int>(return);
             take L = LinkedList(ret.node);
             let First_ = Dll_First(L);
             let Rest_ = Dll_Rest(L);
             let node = Dll_Node(L);
             Seq_Node_to_Seq(First_ )== Seq_Node_to_Seq(First) || Seq_Node_to_Seq(Rest_) == Seq_Node_to_Seq(Rest);
             !is_null(ret.node) implies (Seq_Node_to_Seq(First_ ) == Seq_Node_to_Seq(First) implies Seq_Node_to_Seq(Rest) == Seq_Cons{head: node.data, tail: Seq_Node_to_Seq(Rest_)});

             !is_null(ret.node) implies (Seq_Node_to_Seq(Rest_ ) == Seq_Node_to_Seq(Rest) implies Seq_Node_to_Seq(First) == Seq_Cons{head: node.data, tail: Seq_Node_to_Seq(First_)});

             Seq_Node_to_Seq(First) == Seq_Cons{head: node.data, tail: Seq_Node_to_Seq(First_)} || Seq_Node_to_Seq(Rest) == Seq_Cons{head: node.data, tail: Seq_Node_to_Seq(Rest_)} || (Seq_Node_to_Seq(First) == Seq_Nil{} && Seq_Node_to_Seq(Rest) == Seq_Nil{});

            //  flatten(l) == append(rev(nodeSeqtoSeq(first)), nodeSeqtoSeq(rest));

@*/
{
    if (n == 0) { //empty list case
        struct node_and_int *pair = malloc_node_and_int();
        pair->node = 0;  //null pointer
        pair->data = 0;
        return pair;
    } else { 
        struct node *temp = 0;
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

        struct node_and_int *pair = malloc_node_and_int();
        pair->node = temp;
        pair->data = n->data;

        free_node(n);       
        return pair;
    }
}

struct node *find_head_aux(struct node *n)
/*@ requires !is_null(n);
             take node = Owned<struct node>(n);
             take L = Own_Backwards(node.prev, n, node);
    ensures take node_ = Owned<struct node>(n);
            take L_ = Own_Backwards(node_.prev, n, node_);
            node == node_;
            L == L_;
@*/
{
    /*@ split_case(is_null(n)); @*/
    /*@ split_case(is_null((*n).prev)); @*/
    if (n->prev == 0)
    {
        return n;
    } else {
        /*@ split_case(is_null((*(*n).prev).prev)); @*/
        return find_head_aux(n->prev);
    }
}

// Takes any node in the list and returns the head of the list
// TODO: correctness check
struct node *find_head(struct node *n)
/*@ requires take L = LinkedList(n);
    ensures  take L_ = LinkedList(n);
             L == L_;
@*/
{
   /*@ split_case(is_null(n)); @*/
    if (n == 0)
    {
        return 0;
    } else {
        /*@ split_case(is_null((*n).prev)); @*/
        return find_head_aux(n);
    }
}


struct node *find_tail_aux(struct node *n)
/*@ requires !is_null(n);
             take node = Owned<struct node>(n);
             take L = Own_Forwards(node.next, n, node);
    ensures take node_ = Owned<struct node>(n);
            take L_ = Own_Forwards(node_.next, n, node_);
            node == node_;
            L == L_;
@*/
{
    /*@ split_case(is_null(n)); @*/
    /*@ split_case(is_null((*n).next)); @*/
    if (n->next == 0)
    {
        return n;
    } else {
        /*@ split_case(is_null((*(*n).next).next)); @*/
        return find_tail_aux(n->next);
    }
}

// Takes any node in the list and returns the tail of the list
// TODO: correctness check
struct node *findTail(struct node *n)
/*@ requires take L = LinkedList(n);
    ensures  take L_ = LinkedList(n);
             L == L_;
@*/
{
   /*@ split_case(is_null(n)); @*/
    if (n == 0)
    {
        return 0;
    } else {
        /*@ split_case(is_null((*n).next)); @*/
        return find_tail_aux(n);
    }
}
