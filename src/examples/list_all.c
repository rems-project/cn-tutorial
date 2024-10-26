#ifndef CN_UTILS
#include <stdlib.h>
void *cn_malloc(unsigned long size);
void cn_free_sized(void* p, unsigned long s);
#endif

void freeUnsignedInt(unsigned int *p)
/*@ trusted;
  requires take v = Block<unsigned int>(p);
  ensures true; @*/
{
    cn_free_sized(p, sizeof(int));
}

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



// append.h

/*@
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
@*/



/*@
function [rec] (datatype seq) snoc(datatype seq xs, i32 y) {
  match xs {
    Seq_Nil {} => {
      Seq_Cons {head: y, tail: Seq_Nil{}}
    }
    Seq_Cons {head: x, tail: zs}  => {
      Seq_Cons{head: x, tail: snoc (zs, y)}
    }
  }
}
@*/


/*@
function [rec] (datatype seq) rev(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : h, tail : zs}  => {
      snoc (rev(zs), h)
    }
  }
}
@*/


/*@
lemma append_nil_r (datatype seq l1)
  requires true;
  ensures append(l1, Seq_Nil {}) == l1;

lemma append_cons_r (datatype seq l1, i32 x, datatype seq l2)
  requires true;
  ensures append(l1, Seq_Cons {head: x, tail: l2})
          == append(snoc(l1, x), l2);
@*/


struct int_list* IntList_rev_loop(struct int_list *xs)
/*@ requires take L = IntList(xs);
    ensures  take L_ = IntList(return);
             L_ == rev(L);
@*/
{
  struct int_list *last = 0;
  struct int_list *cur = xs;
  /*@ apply append_nil_r(rev(L)); @*/
  while(1)
  /*@ inv take L1 = IntList(last);
          take L2 = IntList(cur);
          append(rev(L2), L1) == rev(L);
  @*/
  {
    if (cur == 0) {
      /*@ unfold rev(Seq_Nil {}); @*/
      /*@ unfold append(Seq_Nil {}, L1); @*/
      return last;
    }
    struct int_list *tmp = cur->tail;
    cur->tail = last;
    last = cur;
    cur = tmp;
    /*@ unfold rev(L2); @*/
    /*@ apply append_cons_r (rev (tl(L2)), hd(L2), L1); @*/
  }
}

struct int_list* IntList_copy (struct int_list *xs)
/*@ requires take L1 = IntList(xs);
    ensures take L1_ = IntList(xs);
            take L2 = IntList(return);
            L1 == L1_;
            L1 == L2;
@*/
{
  if (xs == 0) {
    return IntList_nil();
  } else {
    struct int_list *new_tail = IntList_copy(xs->tail);
    return IntList_cons(xs->head, new_tail);
  }
}

void IntList_free_list(struct int_list* xs)
// You fill in the rest...
/* --BEGIN-- */
/*@ requires take L1 = IntList(xs); @*/
{
  if (xs == 0) {
  } else {
    IntList_free_list(xs->tail);
    freeIntList(xs);
  }
}
/* --END-- */

/* --BEGIN-- */
/*@
function [rec] (u32) length(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0u32
    }
    Seq_Cons {head : h, tail : zs}  => {
      1u32 + length(zs)
    }
  }
}
@*/

/* --END-- */
unsigned int IntList_length (struct int_list *xs)
/* --BEGIN-- */
/*@ requires take L1 = IntList(xs);
    ensures take L1_ = IntList(xs);
            L1 == L1_;
            return == length(L1);
@*/
/* --END-- */
{
  if (xs == 0) {
/* --BEGIN-- */
    /*@ unfold length(L1); @*/
/* --END-- */
    return 0;
  } else {
/* --BEGIN-- */
    /*@ unfold length(L1); @*/
/* --END-- */
    return 1 + IntList_length (xs->tail);
  }
}


struct int_list* IntList_rev_aux(struct int_list* xs, struct int_list* ys)
/*@ requires take L1 = IntList(xs); @*/
/*@ requires take L2 = IntList(ys); @*/
/*@ ensures take R = IntList(return); @*/
/*@ ensures R == append(rev(L2), L1); @*/
{
  if (ys == 0) {
    /*@ unfold rev(L2); @*/
    /*@ unfold append(Seq_Nil {},L1); @*/
    return xs;
  } else {
    /*@ unfold rev(L2); @*/
    /*@ apply append_cons_r(rev(tl(L2)), hd(L2), L1); @*/
    struct int_list *tmp = ys->tail;
    ys->tail = xs;
    return IntList_rev_aux(ys, tmp);
  }
}

struct int_list* IntList_rev(struct int_list* xs)
/*@ requires take L1 = IntList(xs); @*/
/*@ ensures take L1_rev = IntList(return); @*/
/*@ ensures L1_rev == rev(L1); @*/
{
  /*@ apply append_nil_r(rev(L1)); @*/
  return IntList_rev_aux (0, xs);
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

function [rec] (datatype seq) cn_mergesort(datatype seq xs) {
  match xs {
      Seq_Nil{} => { xs }
      Seq_Cons{head: x, tail: Seq_Nil{}} => { xs }
      Seq_Cons{head: x, tail: Seq_Cons{head: y, tail: zs}} => {
        let P = split(xs);
        let L1 = cn_mergesort(P.fst);
        let L2 = cn_mergesort(P.snd);
        merge(L1, L2)
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
/*@ ensures Ys == cn_mergesort(Xs); @*/
{
  if (xs == 0) {
    /*@ unfold cn_mergesort(Xs); @*/
    return xs;
  } else {
    struct int_list *tail = xs->tail;
    if (tail == 0) {
      /*@ unfold cn_mergesort(Xs); @*/
      return xs;
    } else {
      /*@ unfold cn_mergesort(Xs); @*/
      struct int_list_pair p = IntList_split(xs);
      p.fst = IntList_mergesort(p.fst);
      p.snd = IntList_mergesort(p.snd);
      return IntList_merge(p.fst, p.snd);
    }
  }
}


unsigned int *mallocUnsignedInt()
/*@ trusted;
    ensures take v = Block<unsigned int>(return); !is_null(return); @*/
{
    return cn_malloc(sizeof(unsigned int));
}

unsigned int *refUnsignedInt (unsigned int v)
/*@ ensures take vr = Owned(return);
            vr == v;
@*/
{
    unsigned int *res = mallocUnsignedInt();
    *res = v;
    return res;
}

void IntList_length_acc_aux (struct int_list *xs, unsigned int *p)
/*@ requires take L1 = IntList(xs);
             take n = Owned<unsigned int>(p);
    ensures take L1_ = IntList(xs);
            take n_ = Owned<unsigned int>(p);
            L1 == L1_;
            n_ == n + length(L1);
@*/
{
  /*@ unfold length(L1); @*/
  if (xs == 0) {
  } else {
    *p = *p + 1;
    IntList_length_acc_aux (xs->tail, p);
  }
}

void assert_12357(struct int_list *xs)
/*@ trusted;
    requires take L1 = IntList(xs);
                L1 ==       Seq_Cons {
                    head: 1i32 , tail: Seq_Cons {
                    head: 2i32 , tail: Seq_Cons {
                    head: 3i32 , tail: Seq_Cons {
                    head: 5i32 , tail: Seq_Cons {
                    head: 7i32 , tail: Seq_Nil {} }}}}};
    ensures take L1_ = IntList(xs);
            L1 == L1_;
@*/
{
}

unsigned int IntList_length_acc (struct int_list *xs)
/*@ requires take L1 = IntList(xs);
    ensures take L1_ = IntList(xs);
            L1 == L1_;
            return == length(L1);
@*/
{
  unsigned int *p = refUnsignedInt(0);
  IntList_length_acc_aux(xs, p);
  unsigned int x = *p;
  freeUnsignedInt(p);
  return x;
}

struct int_list* IntList_append(struct int_list* xs, struct int_list* ys)
/*@ requires take L1 = IntList(xs); @*/
/*@ requires take L2 = IntList(ys); @*/
/*@ ensures take L3 = IntList(return); @*/
/*@ ensures L3 == append(L1, L2); @*/
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

struct int_list* IntList_append2 (struct int_list *xs, struct int_list *ys)
/* --BEGIN-- */
/*@ requires take L1 = IntList(xs); @*/
/*@ requires take L2 = IntList(ys); @*/
/*@ ensures take L1_ = IntList(xs); @*/
/*@ ensures take L2_ = IntList(ys); @*/
/*@ ensures take L3 = IntList(return); @*/
/*@ ensures L3 == append(L1, L2); @*/
/*@ ensures L1 == L1_; @*/
/*@ ensures L2 == L2_; @*/
/* --END-- */
{
  if (xs == 0) {
/* --BEGIN-- */
    /*@ unfold append(L1, L2); @*/
/* --END-- */
    return IntList_copy(ys);
  } else {
/* --BEGIN-- */
    /*@ unfold append(L1, L2); @*/
/* --END-- */
    struct int_list *new_tail = IntList_append2(xs->tail, ys);
    return IntList_cons(xs->head, new_tail);
  }
}

int main()
/*@ trusted; @*/
{
    struct int_list* list = IntList_nil();
    list = IntList_cons(3, list);
    list = IntList_cons(5, list);
    list = IntList_cons(2, list);
    list = IntList_cons(7, list);
    list = IntList_cons(1, list);
    
    unsigned int len = IntList_length(list);
    /*@ assert (len == 5u32); @*/

    struct int_list *copied = IntList_copy(list);
    len = IntList_length(copied);
    /*@ assert (len == 5u32); @*/

    struct int_list *rev = IntList_rev_loop(copied);
    struct int_list *rev_rev = IntList_rev(rev);
    len = IntList_length(rev_rev);
    /*@ assert (len == 5u32); @*/

    struct int_list *merged = IntList_mergesort(list);
    assert_12357(merged);

    unsigned int acc =IntList_length_acc(list);
    /*@ assert (acc == 5u32); @*/

    IntList_free_list(rev_rev);

    struct int_list num3 = { .head = 3, .tail = 0 };
    struct int_list num2 = { .head = 2, .tail = &num3 };
    struct int_list num1 = { .head = 1, .tail = &num2 };

    struct int_list ys = { .head = 4, .tail = 0 };

    struct int_list *res = IntList_append2(&num1, &ys);

    struct int_list *res1 = IntList_append(0, &ys);

    struct int_list *res2 = IntList_append(&num1, &ys);

}
