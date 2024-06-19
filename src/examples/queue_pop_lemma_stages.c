#include "queue_headers.h"

// Step 1: Understand the state we have upon lemma entry accurately.
//         This is a sanity check that keeps your lemmas honest.

/*@

predicate (datatype seq) Pre(pointer front, pointer back, i32 popped, datatype seq before) {
  if (is_null(front)) {
    let after = Seq_Nil{};
    assert (before == snoc(Seq_Nil{}, popped));
    return after;
  } else {
    take B = Owned<struct int_queueCell>(back);
    assert (is_null(B.next));
    take L = IntQueueAux (front, back);
    assert (before == snoc(Seq_Cons {head: popped, tail: L}, B.first));
    let after = snoc(L, B.first);
    return after;
  }
}

lemma lemma1(pointer front, pointer back, i32 popped, datatype seq before)
requires
    take Q = Pre(front, back, popped, before);
ensures
    take NewQ = Pre(front, back, popped, before);
    Q == NewQ;
@*/

// Step 2: Copy the state into the post-condition, adding the asserts the SMT solver can't manage.

/*@

predicate (datatype seq) Post(pointer front, pointer back, i32 popped, datatype seq before) {
  if (is_null(front)) {
    assert (before == snoc(Seq_Nil{}, popped));
    let after = Seq_Nil{};
    assert (after == tl(before));
    assert (popped == hd(before));
    return after;
  } else {
    take B = Owned<struct int_queueCell>(back);
    assert (is_null(B.next));
    take L = IntQueueAux (front, back);
    assert (before == snoc(Seq_Cons {head: popped, tail: L}, B.first));
    let after = snoc(L, B.first);
    assert (after == tl(before));
    assert (popped == hd(before));
    return after;
  }
}

lemma lemma2(pointer front, pointer back, i32 popped, datatype seq before)
requires
    take Q = Pre(front, back, popped, before);
ensures
    take NewQ = Post(front, back, popped, before);
    Q == NewQ;
@*/

// Step 3: Expose the values of the predicate you wish to constrain as an output.
//         Arguments used for only for the sanity check are now deleted from the predicate.
//         Assertions are moved outside the predicate, and into the lemma.

/*@

type_synonym result = { datatype seq after, datatype seq before }

predicate (result) Queue_pop_lemma(pointer front, pointer back, i32 popped) {
  if (is_null(front)) {
    return { after: Seq_Nil{}, before: snoc(Seq_Nil{}, popped) };
  } else {
    take B = Owned<struct int_queueCell>(back);
    assert (is_null(B.next));
    take L = IntQueueAux (front, back);
    return { after: snoc(L, B.first), before: snoc(Seq_Cons {head: popped, tail: L}, B.first) };
  }
}

lemma lemma3(pointer front, pointer back, i32 popped, datatype seq before)
requires
    take Q = Queue_pop_lemma(front, back, popped);
    before == Q.before;
ensures
    take NewQ = Queue_pop_lemma(front, back, popped);
    Q == NewQ;
    Q.after == tl(Q.before);
    popped == hd(Q.before);
@*/

// Step 4 (optional): Remove the sanity checking from the pre-condition.

/*@

lemma snoc_fact_unified(pointer front, pointer back, i32 popped)
requires
    take Q = Queue_pop_lemma(front, back, popped);
ensures
    take NewQ = Queue_pop_lemma(front, back, popped);
    Q == NewQ;
    Q.after == tl(Q.before);
    popped == hd(Q.before);

@*/
