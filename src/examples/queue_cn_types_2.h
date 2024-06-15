/*@
predicate (datatype seq) IntQueueFB (pointer front, pointer back) {
  if (is_null(front)) {
    return Seq_Nil{};
  } else {
    take T = Owned<struct int_queueCell>(back);
    assert (is_null(T.next));
    take Q = IntQueueAux (front, back);
    return snoc(Q, T.first);
  }
}
@*/
