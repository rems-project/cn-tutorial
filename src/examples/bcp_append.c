struct int_list {
  int head;
  struct int_list* tail;
};

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}

function [rec] (datatype seq) append(datatype seq xs, datatype seq ys) {
  match xs {
    Seq_Nil {} => {
      ys
    }
    Seq_Cons {head : h, tail : zs}  => {
      Seq_Cons {head: h, tail: append(zs, ys)}
    }
  }
}

predicate (datatype seq) IntList(pointer p) {
  if (is_null(p)) {
    return Seq_Nil{};
  } else {
    take H = Owned<struct int_list>(p);
    assert (is_null(H.tail) || (u64)H.tail != 0u64);
    take tl = IntList(H.tail);
    return (Seq_Cons { head: H.head, tail: tl });
  }
}
@*/

struct int_list* IntList_append(struct int_list* xs, struct int_list* ys)
/*@ requires take L1 = IntList(xs) @*/
/*@ requires take L2 = IntList(ys) @*/
/*@ ensures take L3 = IntList(return) @*/
/*@ ensures L3 == append(L1, L2) @*/
{
  if (xs == 0) {
    /*@ unfold append(L1, L2); @*/
    return ys;
  } else {
    /*@ unfold append(L1, L2); @*/
    struct int_list *new_tail = IntList_append(xs->tail, ys);
    xs->tail = new_tail;
    return xs;
  }
}

/*@
function [rec] ({datatype seq fst, datatype seq snd}) split(datatype seq xs)
{
  match xs {
    Seq_Nil {} => {
      {fst: Seq_Nil{}, snd: Seq_Nil{}}
    }
    Seq_Cons {head: h1, tail: Seq_Nil{}} => {
      {fst: Seq_Nil{}, snd: xs}
    }
    Seq_Cons {head: h1, tail: Seq_Cons {head : h2, tail : tl2 }} => {
      let P = split(tl2);
      {fst: Seq_Cons { head: h1, tail: P.fst},
       snd: Seq_Cons { head: h2, tail: P.snd}}
    }
  }
}
@*/
