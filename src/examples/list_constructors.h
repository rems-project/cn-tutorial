struct sllist* slnil()
/*@ ensures take Ret = SLList(return);
            Ret == Nil{};
 @*/
{
  return 0;
}

struct sllist* slcons(int h, struct sllist* t)
/*@ requires take T = SLList(t);
    ensures take Ret = SLList(return);
            Ret == Cons{ Head: h, Tail: T};
 @*/
{
  struct sllist *p = malloc__sllist();
  p->head = h;
  p->tail = t;
  return p;
}
