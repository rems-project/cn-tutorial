#include "list.h"

/*@
function [rec] ({datatype List fst, datatype List snd}) split(datatype List xs)
{
  match xs {
    Nil {} => {
      {fst: Nil{}, snd: Nil{}}
    }
    Cons {Head: h1, Tail: Nil{}} => {
      {fst: Nil{}, snd: xs}
    }
    Cons {Head: h1, Tail: Cons {Head : h2, tail : tl2 }} => {
      let P = split(tl2);
      {fst: Cons { Head: h1, Tail: P.fst},
       snd: Cons { Head: h2, Tail: P.snd}}
    }
  }
}

function [rec] (datatype List) merge(datatype List xs, datatype List ys) {
  match xs {
      Nil {} => { ys }
      Cons {Head: x, Tail: xs1} => {
        match ys {
          Nil {} => { xs }
          Cons{ Head: y, Tail: ys1} => {
            (x < y) ?
              (Cons{ Head: x, Tail: merge(xs1, ys) })
            : (Cons{ Head: y, Tail: merge(xs, ys1) })
          }
        }
      }
  }
}

function [rec] (datatype List) mergesort(datatype List xs) {
  match xs {
      Nil{} => { xs }
      Cons{Head: x, Tail: Nil{}} => { xs }
      Cons{Head: x, Tail: Cons{Head: y, Tail: zs}} => {
        let P = split(xs);
        let L1 = mergesort(P.fst);
        let L2 = mergesort(P.snd);
        merge(L1, L2)
      }
    }
}
@*/

struct int_list_pair {
  struct int_list* fst;
  struct int_list* snd;
};

struct int_list_pair split(struct int_list *xs)
/*@ requires take Xs = SLList(xs); @*/
/*@ ensures take Ys = SLList(return.fst); @*/
/*@ ensures take Zs = SLList(return.snd); @*/
/*@ ensures {fst: Ys, snd: Zs} == split(Xs); @*/
{
  if (xs == 0) {
    /*@ unfold split(Xs); @*/
    struct int_list_pair r = {.fst = 0, .snd = 0};
    return r;
  } else {
    struct int_list *cdr = xs -> tail;
    if (cdr == 0) {
      /*@ unfold split(Xs); @*/
      struct int_list_pair r = {.fst = 0, .snd = xs};
      return r;
    } else {
      /*@ unfold split(Xs); @*/
      struct int_list_pair p = split(cdr->tail);
      xs->tail = p.fst;
      cdr->tail = p.snd;
      struct int_list_pair r = {.fst = xs, .snd = cdr};
      return r;
    }
  }
}

struct int_list* merge(struct int_list *xs, struct int_list *ys)
/*@ requires take Xs = SLList(xs); @*/
/*@ requires take Ys = SLList(ys); @*/
/*@ ensures take Zs = SLList(return); @*/
/*@ ensures Zs == merge(Xs, Ys); @*/
{
  if (xs == 0) {
    /*@ unfold merge(Xs, Ys); @*/
    return ys;
  } else {
    /*@ unfold merge(Xs, Ys); @*/
    if (ys == 0) {
      /*@ unfold merge(Xs, Ys); @*/
      return xs;
    } else {
      /*@ unfold merge(Xs, Ys); @*/
      if (xs->head < ys->head) {
        struct int_list *zs = merge(xs->tail, ys);
        xs->tail = zs;
        return xs;
      } else {
        struct int_list *zs = merge(xs, ys->tail);
        ys->tail = zs;
        return ys;
      }
    }
  }
}

struct int_list* mergesort(struct int_list *xs)
/*@ requires take Xs = SLList(xs); @*/
/*@ ensures take Ys = SLList(return); @*/
/*@ ensures Ys == mergesort(Xs); @*/
{
  if (xs == 0) {
    /*@ unfold mergesort(Xs); @*/
    return xs;
  } else {
    struct int_list *tail = xs->tail;
    if (tail == 0) {
      /*@ unfold mergesort(Xs); @*/
      return xs;
    } else {
      /*@ unfold mergesort(Xs); @*/
      struct int_list_pair p = split(xs);
      p.fst = mergesort(p.fst);
      p.snd = mergesort(p.snd);
      return merge(p.fst, p.snd);
    }
  }
}
