/*@
predicate (datatype seq) IntQueueFB (pointer front, pointer back) {
  if (is_null(front)) {
    return Seq_Nil{};
  } else {
    take B = Owned<struct int_queueCell>(back);
    assert (is_null(B.next));
    assert (ptr_eq(front, back) || !addr_eq(front, back));
    take L = IntQueueAux (front, back);
    return snoc(L, B.first);
  }
}
@*/
