// Sorted list

#define ELEMENT unsigned char

struct List
{
  ELEMENT value;
  struct List* next;
};

/*@
type_synonym ELEMENT = u8

datatype IntList {
  Nil {},
  Cons { ELEMENT head, IntList tail }
}

function (boolean) validCons(ELEMENT head, IntList tail) {
  match tail {
    Nil {} => { true }
    Cons { head: next, tail: _ } => { head <= next }
  }
}

predicate IntList ListSegment(pointer from, pointer to) {
  if (ptr_eq(from,to)) {
    return Nil {};
  } else {
    take head = Owned<struct List>(from);
    take tail = ListSegment(head.next, to);
    assert(validCons(head.value,tail));
    return Cons { head: head.value, tail: tail };
  }
}
@*/


void *cn_malloc(unsigned long size);

// This is invalid because we don't preserve the sorted invariant.
void cons(ELEMENT x, struct List** xs)
/*@
  requires
    take list_ptr = Owned<struct List*>(xs);
    take list = ListSegment(list_ptr,NULL);
  ensures
    take new_list_ptr = Owned<struct List*>(xs);
    take new_list = ListSegment(new_list_ptr,NULL);
@*/
{
  struct List *node = (struct List*) cn_malloc(sizeof(struct List));
  node->value = x;
  node->next = *xs;
  *xs = node;
}
