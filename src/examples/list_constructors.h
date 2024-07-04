struct int_list* IntList_nil()
/*@ ensures take ret = IntList(return);
            ret == Seq_Nil{};
 @*/
{
  return 0;
}

struct int_list* IntList_cons(int h, struct int_list* t)
/*@ requires take l = IntList(t);
    ensures take ret = IntList(return);
            ret == Seq_Cons{ head: h, tail: l};
 @*/
{
  struct int_list *p = mallocIntList();
  p->head = h;
  p->tail = t;
  return p;
}
