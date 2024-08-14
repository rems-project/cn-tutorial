/*@
predicate (datatype List) IntQueueFB (pointer front, pointer back) {
  if (is_null(front)) {
    return Nil{};
  } else {
    take B = Owned<struct int_queueCell>(back);
    assert (is_null(B.next));
    take L = IntQueueAux (front, back);
    return Snoc(L, B.first);
  }
}
@*/
