/* A version of doubly linked lists that is essentially from Reynold's
   original separation logic paper (https://www.cs.cmu.edu/~jcr/seplogic.pdf).
   Page 10 has his definition of doubly-linked lists (dlist).

   They're slightly different from ours in that they're "open":
   there's no special treatment of null for the front of the list.

   Technical note for the future: We could eliminate the hacky
   assert_not_equal reasoning if we added this lemma:

      lemma assert_not_equal (p, prev, cur, f, b)
        requires Own_Fwd(prev, cur, f, b);
                        Owned<struct node>(p);
        ensures Own_Fwd(prev, cur, f, b);
                        Owned<struct node>(p);
                        !ptr_eq(p,b);

   This more specific lemma is something we could actually
   (eventually) prove in Rocq, as an inductive fact derived from the
   resource predicate definition. */

struct node {
    int data;
    struct node *prev;
    struct node *next;
};

struct dbl_queue {
    struct node *front;
    struct node *back;
};

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}

predicate (datatype seq) Dbl_Queue_Fwd_At (pointer l) {
    take L = Owned<struct dbl_queue>(l);
    assert(   (is_null(L.front)  && is_null(L.back))
           || (!is_null(L.front) && !is_null(L.back)));
    take inner = Own_Fwd (L.front, NULL, L.back);
    return inner;
}

predicate (datatype seq) Own_Fwd
              (pointer curr, pointer prev, pointer b) {
    if (is_null(curr)) {
        return Seq_Nil{};
    } else {
        take Curr = Owned<struct node>(curr);
        assert(ptr_eq(Curr.prev, prev));
        assert(ptr_eq(curr,b) implies is_null(Curr.next));
        take Rest = Own_Fwd(Curr.next, curr, b);
        return Seq_Cons{head: Curr.data, tail: Rest};
    }
}

lemma assert_not_equal (pointer x, pointer y)
  requires true;
  ensures !ptr_eq(x,y);
@*/

extern struct node *malloc_node();
/*@ spec malloc_node();
    requires true;
    ensures take u = Block<struct node>(return);
@*/

void push_front (struct dbl_queue* q, int element)
/*@ requires take Before = Dbl_Queue_Fwd_At(q);
    ensures  take After = Dbl_Queue_Fwd_At(q);
             After == Seq_Cons{head: element, tail: Before};
@*/
{
    struct node *new_node = malloc_node();
    /*@ apply assert_not_equal(new_node, q->front); @*/
    /*@ apply assert_not_equal(new_node, q->back); @*/
    new_node->data = element;
    new_node->next = q->front;
    new_node->prev = 0;

    if (q->front == 0) {
        q->back = new_node;
        q->front = new_node;
        return;
    } else {
        q->front->prev = new_node;
        q->front = new_node;
        return;
    }
}
