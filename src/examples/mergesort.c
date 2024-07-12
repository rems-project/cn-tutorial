#ifndef CN_UTILS
void *cn_malloc(unsigned long);
void cn_free_sized(void* p, unsigned long s);
#endif

struct int_list {
  int head;
  struct int_list* tail;
};

struct int_list *mallocIntList()
/*@ trusted;
    requires true;
    ensures take u = Block<struct int_list>(return);
            !ptr_eq(return, NULL);
@*/
{
    return cn_malloc(sizeof(struct int_list));
}

void freeIntList (struct int_list *p)
/*@ trusted;
    requires take u = Block<struct int_list>(p);
    ensures true;
@*/
{
    cn_free_sized(p, sizeof(struct int_list));
}


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


/*@
function (i32) hd (datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0i32
    }
    Seq_Cons {head : h, tail : _} => {
      h
    }
  }
}

function (datatype seq) tl (datatype seq xs) {
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


struct int_list* IntList_nil()
/*@ ensures take ret = IntList(return);
            ret == Seq_Nil{};
 @*/
{
  return 0;
}

struct int_list* IntList_cons(int h, struct int_list* t)
/*@ requires take l = IntList(t);
    ensures take ret = IntList(return);
            ret == Seq_Cons{ head: h, tail: l};
 @*/
{
  struct int_list *p = mallocIntList();
  p->head = h;
  p->tail = t;
  return p;
}



/*@
datatype SplitDT {
   Pair { datatype seq fst, datatype seq snd }
}

function [rec] (datatype SplitDT) split(datatype seq xs)
{
  match xs {
    Seq_Nil {} => {
      Pair {fst: Seq_Nil{}, snd: Seq_Nil{}}
    }
    Seq_Cons {head: h1, tail: Seq_Nil{}} => {
      Pair {fst: Seq_Nil{}, snd: xs}
    }
    Seq_Cons {head: h1, tail: Seq_Cons {head : h2, tail : tl2 }} => {
    match (split(tl2)) {
        Pair { fst : fst , snd : snd } => { Pair {
            fst: Seq_Cons { head: h1, tail: fst},
            snd: Seq_Cons { head: h2, tail: snd}
        } }
      }
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
        match (split(xs)) {
        Pair { fst : fst , snd : snd } => {
            let L1 = mergesort(fst);
            let L2 = mergesort(snd);
            merge(L1, L2)
          }
        }
      }
    }
}
@*/

struct int_list_pair {
  struct int_list* fst;
  struct int_list* snd;
};

struct int_list_pair IntList_split(struct int_list *xs)
/*@ requires take Xs = IntList(xs); @*/
/*@ ensures take Ys = IntList(return.fst); @*/
/*@ ensures take Zs = IntList(return.snd); @*/
/*@ ensures Pair {fst: Ys, snd: Zs} == split(Xs); @*/
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
      struct int_list_pair p = IntList_split(cdr->tail);
      xs->tail = p.fst;
      cdr->tail = p.snd;
      struct int_list_pair r = {.fst = xs, .snd = cdr};
      return r;
    }
  }
}

struct int_list* IntList_merge(struct int_list *xs, struct int_list *ys)
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
        struct int_list *zs = IntList_merge(xs->tail, ys);
        xs->tail = zs;
        return xs;
      } else {
        struct int_list *zs = IntList_merge(xs, ys->tail);
        ys->tail = zs;
        return ys;
      }
    }
  }
}

struct int_list* IntList_mergesort(struct int_list *xs)
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
      struct int_list_pair p = IntList_split(xs);
      p.fst = IntList_mergesort(p.fst);
      p.snd = IntList_mergesort(p.snd);
      return IntList_merge(p.fst, p.snd);
    }
  }
}

int main()
/*@ trusted; @*/
{
}
