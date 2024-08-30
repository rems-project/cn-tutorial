/*@
predicate (datatype List) IntQueuePtr (pointer q) {
  take Q = Owned<struct queue>(q);
  assert (   (is_null(Q.front)  && is_null(Q.back)) 
          || (!is_null(Q.front) && !is_null(Q.back)));
  take L = IntQueueFB(Q.front, Q.back);
  return L;
}
@*/
