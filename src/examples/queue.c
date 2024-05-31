/* queue.c */

#include "list.h"
#include "list_rev_spec.h"  /* (For snoc) */

/*@
function [rec] (datatype seq) push (datatype seq xs, i32 y) {
  snoc (xs, y)
}

function [rec] (i32) pop (datatype seq xs, i32 y) {
  hd (xs)
}

@*/

struct int_queue {
  struct int_queueCell* head;
  struct int_queueCell* tail;
};

extern struct int_queue *mallocIntQueue();
/*@ spec mallocIntQueue();
    requires true;
    ensures take u = Block<struct int_queue>(return);
            return != NULL;
@*/ // 'return != NULL' should not be needed

extern void freeIntQueue (struct int_queue *p);
/*@ spec freeIntQueue(pointer p);
    requires take u = Block<struct int_queue>(p);
    ensures true;
@*/

struct int_queueCell {
  int this;
  struct int_queueCell* next;
};

extern struct int_queueCell *mallocIntQueueCell();
/*@ spec mallocIntQueueCell();
    requires true;
    ensures take u = Block<struct int_queueCell>(return);
            return != NULL;
@*/ // 'return != NULL' should not be needed

extern void freeIntQueueCell (struct int_queueCell *p);
/*@ spec freeIntQueueCell(pointer p);
    requires take u = Block<struct int_queueCell>(p);
    ensures true;
@*/

