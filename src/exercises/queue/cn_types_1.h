/*@
predicate (datatype List) QueuePtr_At (pointer q) {
  take Q = RW<struct queue>(q);
  assert (   (is_null(Q.front)  && is_null(Q.back)) 
          || (!is_null(Q.front) && !is_null(Q.back)));
  take L = QueueFB(Q.front, Q.back);
  return L;
}
@*/
