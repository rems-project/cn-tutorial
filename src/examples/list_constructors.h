struct sllist* nil__sllist()
/*@ ensures take Ret = Linked_List_Int(return);
            Ret == Nil__Seq_Int{};
 @*/
{
  return 0;
}

struct sllist* cons__sllist(int h, struct sllist* t)
/*@ requires take T = Linked_List_Int(t);
    ensures take Ret = Linked_List_Int(return);
            Ret == Cons__Seq_Int{ Head: h, Tail: T};
 @*/
{
  struct sllist *p = malloc_sllist();
  p->head = h;
  p->tail = t;
  return p;
}
