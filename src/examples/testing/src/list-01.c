

struct List
{
  int value;
  struct List* next;
};

/*@
datatype IntList {
  Nil {},
  Cons { i32 head, IntList tail }
}

predicate IntList ListSegment(pointer from, pointer to) {
  if (ptr_eq(from,to)) {
    return Nil {};
  } else {
    take head = Owned<struct List>(from);
    take tail = ListSegment(head.next, to);
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


// This is an invalid spec, list is modified.
int sum_and_modify(struct List* xs)
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
    xs->value = 7;
    xs = xs->next;
  }
  return result;
}