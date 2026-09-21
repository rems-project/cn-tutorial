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

// This is a valid spec, even though to verify with CN we'd need a loop invariant.
int sum(struct List* xs)
/*@
  requires
    take l1 = ListSegment(xs,NULL);
  ensures
    take l2 = ListSegment(xs,NULL);
    l1 == l2;
    true;
@*/
{
  int result = 0;
  while(xs) {
    result += xs->value;
    xs = xs->next;
  }
  return result;
}

