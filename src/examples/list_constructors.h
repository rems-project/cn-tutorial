struct list_int* nil__list_int()
/*@ ensures take Ret = Linked_List_Int(return);
            Ret == Nil__Seq_Int{};
 @*/
{
  return 0;
}

struct list_int* cons__list_int(int h, struct list_int* t)
/*@ requires take L = Linked_List_Int(t);
    ensures take Ret = Linked_List_Int(return);
            Ret == Cons__Seq_Int{ Head: h, Tail: L};
 @*/
{
  struct list_int *p = malloc_list_int();
  p->head = h;
  p->tail = t;
  return p;
}
