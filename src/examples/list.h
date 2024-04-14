// list.h

#ifndef _LIST_H
#define _LIST_H

struct int_list {
  int head;
  struct int_list* tail;
};

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}

predicate (datatype seq) IntList(pointer p) {
  if (is_null(p)) {
    return Seq_Nil{};
  } else {
    take H = Owned<struct int_list>(p);
    take tl = IntList(H.tail);
    return (Seq_Cons { head: H.head, tail: tl });
  }
}
@*/

struct int_list* IntList_nil()
/*@ ensures take ret = IntList(return);
            ret == Seq_Nil{}
 @*/
{
  return 0;
}

struct int_list* IntList_cons(int h, struct int_list* t)
/*@ trusted
    requires take l = IntList(t)
    ensures take ret = IntList(return);
            ret == Seq_Cons{ head: h, tail: l}
 @*/
{
  // (a raw, unchecked call to malloc goes here)
}

void IntList_free(struct int_list* p)
/*@ trusted
    requires take H = Owned<struct int_list>(p)
 @*/
{
  // (a raw, unchecked call to free goes here)
}


/*@
function (i32) hd(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0i32
    }
    Seq_Cons {head : h, tail : _} => {
      h
    }
  }
}

function (datatype seq) tl(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : _, tail : tail} => {
      tail
    }
  }
}
@*/

#endif//_LIST_H
