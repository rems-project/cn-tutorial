#include "list.h"

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

function [rec] (datatype seq) merge(datatype seq xs, datatype seq ys) {
  match xs {
      Seq_Nil {} => { ys }
      Seq_Cons {head: x, tail: xs1} => {
        match ys {
          Seq_Nil {} => { xs }
          Seq_Cons{ head: y, tail: ys1} => {
            (x < y) ?
              (Seq_Cons{ head: x, tail: merge(xs1, ys) })
            : (Seq_Cons{ head: y, tail: merge(xs, ys1) })
          }
        }
      }
  }
}

function [rec] (datatype seq) mergesort(datatype seq xs) {
  match xs {
      Seq_Nil{} => { xs }
      Seq_Cons{head: x, tail: Seq_Nil{}} => { xs }
      Seq_Cons{head: x, tail: Seq_Cons{head: y, tail: zs}} => {
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
/*@ requires take Xs = IntList(xs); @*/
/*@ ensures take Ys = IntList(return.fst); @*/
/*@ ensures take Zs = IntList(return.snd); @*/
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
/*@ requires take Xs = IntList(xs); @*/
/*@ requires take Ys = IntList(ys); @*/
/*@ ensures take Zs = IntList(return); @*/
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
/*@ requires take Xs = IntList(xs); @*/
/*@ ensures take Ys = IntList(return); @*/
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
