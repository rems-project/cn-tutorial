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

function [rec] (IntList) insertList(boolean dups, ELEMENT x, IntList xs) {
  match xs {
    Nil {} => { Cons { head: x, tail: Nil {} } }
    Cons { head: head, tail: tail } => {
      if (head < x) {
        Cons { head: head, tail: insertList(dups, x,tail) }
      } else {
        if (!dups && head == x) {
          xs
        } else {
          Cons { head: x, tail: xs }
        }
      }
    }
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

void insert(ELEMENT x, struct List **xs)
/*@
  requires
    take list_ptr = Owned<struct List*>(xs);
    take list = ListSegment(list_ptr,NULL);
  ensures
    take new_list_ptr = Owned<struct List*>(xs);
    take new_list = ListSegment(new_list_ptr,NULL);
    new_list == insertList(true,x,list);
@*/
{
  struct List *node = (struct List*) cn_malloc(sizeof(struct List));
  node->value = x;

  struct List* prev = 0;
  struct List* cur = *xs;
  while (cur && cur->value < x) {
    prev = cur;
    cur = cur->next;
  }

  if (prev) {
    prev->next = node;
    node->next = cur;
  } else {
    node->next = *xs;
    *xs = node;
  }

}
