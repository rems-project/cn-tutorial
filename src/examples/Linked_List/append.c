#include "./headers.h"

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