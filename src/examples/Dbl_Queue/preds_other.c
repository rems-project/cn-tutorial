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
            take Rest = Own_Forwards(F.next, front, F, back, B);
            return Seq_Cons{ head: F.data, tail: snoc(Rest, B.data)};
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
predicate (datatype seq) Own_Forwards(pointer p, pointer prev_pointer, struct node prev_node, pointer b, struct node Back) {
    if (ptr_eq(p,b)) {
        assert(ptr_eq(Back.prev, prev_pointer));
        assert(ptr_eq(prev_node.next, b));
        return Seq_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.prev, prev_pointer));
        assert(ptr_eq(prev_node.next, p));
        assert(!is_null(n.next));
        assert(!is_null(n.prev));
        take Rest = Own_Forwards(n.next, p, n, b, Back);
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
            take Rest = Own_Backwards(B.prev, back, B, front, F);
            return Seq_Cons{ head: B.data, tail: snoc(Rest, F.data)};
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
predicate (datatype seq) Own_Backwards(pointer p, pointer next_pointer, struct node next_node, pointer f, struct node Front) {
    if (ptr_eq(p,f)) {
        assert(ptr_eq(Front.next, next_pointer));
        assert(ptr_eq(next_node.prev, f));
        return Seq_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.next, next_pointer));
        assert(ptr_eq(next_node.prev, p));
        assert(!is_null(n.next));
        assert(!is_null(n.prev));
        take Rest = Own_Backwards(n.prev, p, n, f, Front);
        return Seq_Cons{head: n.data, tail: Rest};
    }
}
@*/