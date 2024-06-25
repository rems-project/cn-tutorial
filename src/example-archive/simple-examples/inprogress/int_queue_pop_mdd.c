// Variant on the queue example in src/examples. Currently doesn't work. 

#include "list.h"
#include "list_snoc_spec.h"

struct int_queue {
  struct int_queueCell* head;
  struct int_queueCell* tail;
};

struct int_queueCell {
  int first;
  struct int_queueCell* next;
};

/*@
predicate (datatype seq) IntQueue(pointer q) {
  take H = Owned<struct int_queue>(q);
  take Q = IntQueue1(q,H);
  return Q;
}

predicate (datatype seq) IntQueue1(pointer dummy, struct int_queue H) {
  if (is_null(H.head)) {
    assert (is_null(H.tail));
    return (Seq_Nil{});
  } else {
    assert (!is_null(H.tail));
    take T = Owned<struct int_queueCell>(H.tail);
    assert (is_null(T.next));
    take Q = IntQueueAux (H.head, H.tail, T.first);
    return Q;
  }
}

predicate (datatype seq) IntQueueAux (pointer h, pointer t, i32 lastVal) {
  if (h == t) {
    return (Seq_Cons{head: lastVal, tail: Seq_Nil{}});
  } else {
    take C = Owned<struct int_queueCell>(h);
    take TL = IntQueueAux(C.next, t, lastVal);
    return (Seq_Cons { head: C.first, tail: TL });
  }
}
@*/

struct int_queueCell* IntQueue_pop (struct int_queue *q)
/*@ requires 
      take HPre = Owned<struct int_queue>(q);
      take FirstPre = Owned<struct int_queueCell>(HPre.head); 
    ensures 
      take HPost = Owned<struct int_queue>(q); 
      HPost.head == FirstPre.next; 
      HPost.tail == (is_null(FirstPre.next) ? FirstPre.next : HPre.tail); 
      take FirstPost = Owned<struct int_queueCell>(HPre.head); 
      return == HPre.head; 
@*/
{
  struct int_queueCell* old_head = q->head; 
  if (q->head->next == 0) {
    q->head = 0;
    q->tail = 0;
  } else {
    q->head = q->head->next;
  }
  return old_head;
}

struct int_queueCell* call_IntQueue_pop(struct int_queue *q) 
/*@ requires 
      take QueuePre = IntQueue(q);
      QueuePre != Seq_Nil{};
    ensures 
      take QueuePost = IntQueue(q);
      take PoppedCell = Owned<struct int_queueCell>(return); 
@*/
{
  /*@ split_case (*q).head == NULL; @*/
  /*@ split_case (*q).head == (*q).tail; @*/
  struct int_queueCell* popped_node = IntQueue_pop(q); 
  return popped_node; 
}

