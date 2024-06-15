/*@
predicate (datatype seq) IntQueuePtr (pointer q) {
  take H = Owned<struct int_queue>(q);
  assert (   (is_null(H.front)  && is_null(H.back)) 
          || (!is_null(H.front) && !is_null(H.back)));
  take Q = IntQueueFB(H.front, H.back);
  return Q;
}
@*/
