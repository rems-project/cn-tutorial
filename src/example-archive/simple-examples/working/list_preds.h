// Definitions here adapted from
// https://github.com/rems-project/cerberus/blob/master/tests/cn/append.c


// A struct representing nodes from a linked list of integers 
struct list_node
{
  int val;
  struct list_node *next;
};

// The specification-level type definition for a sequence. We use this to
// represent the contents of the list.

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons { i32 val, datatype seq next}
}
@*/

// The predicate representing an in-memory list segment. Note that the return
// value of this predicate is the specification-level contents of the list, i.e
// a pure sequence of values.

/*@
predicate (datatype seq) IntListSeg(pointer p, pointer tail) {
  if (addr_eq(p,tail)) {
    return Seq_Nil{};
  } else {
    take H = Owned<struct list_node>(p);
    assert (is_null(H.next) || H.next != NULL);
    take tl = IntListSeg(H.next, tail);
    return (Seq_Cons { val: H.val, next: tl });
  }
}
@*/

// This append function exists at the specification level

/*@
function [rec] (datatype seq) append(datatype seq xs, datatype seq ys) {
  match xs {
    Seq_Nil {} => {
      ys
    }
    Seq_Cons {val : h, next : zs}  => {
      Seq_Cons {val: h, next: append(zs, ys)}
    }
  }
}
@*/

// A lemma saying that a list segment followed by a list node can be folded into
// a list segment. This lemma is assumed by CN and must be proved inductively in
// Coq.
// TODO: as of April 2024, CN cannot export such lemmas to Coq because they
// involve resource predicates. Resolving this would require integration with
// Iris or some other Coq resource logic. 

/*@
lemma IntListSeqSnocVal(pointer p, pointer tail)
  requires take l1 = IntListSeg(p, tail);
           take v = Owned<struct list_node>(tail)
  ensures take l2 = IntListSeg(p, v.next);
          l2 == append(l1, Seq_Cons { val: v.val, next: Seq_Nil {} })
@*/
