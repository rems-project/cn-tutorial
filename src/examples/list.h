// list.h

#ifndef _LIST_H
#define _LIST_H

struct int_list {
  int head;
  struct int_list* tail;
};


extern struct int_list *mallocIntList();
/*@ spec mallocIntList()
    requires true
    ensures take u = Block<struct int_list>(return);
            return != NULL
@*/ // 'return != NULL' should not be needed

extern void freeIntList (struct int_list *p);
/*@ spec freeIntList(pointer p)
    requires take u = Block<struct int_list>(p)
    ensures true
@*/


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
/*@ requires take l = IntList(t)
    ensures take ret = IntList(return);
            ret == Seq_Cons{ head: h, tail: l}
 @*/
{
  struct int_list *p = mallocIntList();
  p->head = h;
  p->tail = t;
  return p;
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
