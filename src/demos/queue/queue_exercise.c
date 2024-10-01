#include <stdlib.h>

/*@
// copying from list_cn_types.h
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}
@*/

#include "../../examples/list_hdtl.h"
#include "../../examples/list_snoc.h"


/*@
// copying from list_length.c
function [rec] (i32) length(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0i32
    }
    Seq_Cons {head : h, tail : zs}  => {
      1i32 + length(zs)
    }
  }
}

function (i32) cn_size (i32 inp, i32 outp, i32 bufsize)
{
  ((inp - outp) + bufsize) % bufsize
}


function [rec] (datatype seq) seq_of_buf (map<i32,i32> buf, i32 inp, i32 outp, i32 bufsize) {
  if (size (inp, outp, bufsize) > 0i32) { 
    Seq_Cons {
      head: buf[outp], 
      tail: seq_of_buf(buf, inp, (outp + 1i32) % bufsize, bufsize)
    } 
  }
  else {
    Seq_Nil {}
  }
}

@*/

typedef struct queue
{
  int inp;
  int outp;
  int size;
  int *buf;
} Queue;

/*@
function (boolean) queue_wf (i32 inp, i32 outp, i32 bufsize)
{
  bufsize > 0i32
  && (i64) bufsize + (i64) bufsize <= 2147483647i64
  && (0i32 <= inp && inp < bufsize)
  && (0i32 <= outp && outp < bufsize)
}

type_synonym impl_state = {
  Queue q, 
  map<i32,i32> buf, 
  datatype seq content,
  i32 size
}

type_synonym state = {
  datatype seq content, 
  i32 size
}

predicate impl_state QueueImpl(pointer p) {
  take q = Owned<Queue>(p);
  take buf = each (i32 i; 0i32 <= i && i < q.size) { Owned<int>(q.buf + i) };
  assert (queue_wf (q.inp, q.outp, q.size));
  let content = seq_of_buf(buf, q.inp, q.outp, q.size);
  return {q: q, buf: buf, content: content, size: q.size - 1i32};
}

predicate state QueueAbs(pointer p)
{
  take i = QueueImpl(p);
  return {content: i.content, size: i.size};
}

@*/


int *malloc_buf(int size)
/*@
  trusted;
  requires true;
  ensures take rv = each (i32 i; 0i32 <= i && i < size) { Owned<int>(return + i) };
@*/
{
  return malloc(size * sizeof(int));
}

Queue *malloc_queue()
/*@
  trusted;
  requires true;
  ensures take rv = Owned<Queue>(return);
@*/
{
  return malloc(sizeof(Queue));
}


// for proof
void prove_queue_empty(struct queue *p)
/*@
requires take i = QueueImpl(p);
ensures take i_out = QueueImpl(p);
        i == i_out;
        let empty = cn_size(i.q.inp, i.q.outp, i.q.size) == 0i32;
        empty ? (seq_of_buf(i.buf, i.q.inp, i.q.outp, i.q.size) == Seq_Nil {}) : true;
@*/
{
  /*@ unfold seq_of_buf(i.buf, i.q.inp, i.q.outp, i.q.size); @*/
}

// for proof
void prove_buf_frame(struct queue *p, int n)
/*@
requires take i = QueueImpl(p);
         let q = i.q;
         cn_size(q.inp, q.outp, q.size) < q.size;
ensures take i_out = QueueImpl(p);
        i == i_out;
        let content_before = seq_of_buf(i.buf, q.inp, q.outp, q.size);
        let content_after = seq_of_buf(i.buf[q.inp: n], q.inp, q.outp, q.size);
        content_after == content_before;
@*/
{
}

void prove_buf_cons(struct queue *p)
/*@
requires take i = QueueImpl(p);
         let q = i.q;
         cn_size(q.inp, q.outp, q.size) < q.size;
ensures take i_out = QueueImpl(p);
        i == i_out;
        let content_before = seq_of_buf(i.buf, q.inp, q.outp, q.size);
        let content_after = seq_of_buf(i.buf, (q.inp+1i32)%q.size, q.outp, q.size);
        content_after == snoc(content_before, i.buf[q.inp]);
@*/
{
}

// for proof
void prove_queue_get(struct queue *p)
/*@
requires take qi = QueueImpl(p);
         let q = qi.q;
         cn_size(q.inp, q.outp, q.size) > 1i32;
ensures take qi_out = QueueImpl(p);
        qi == qi_out;
        let content1 = seq_of_buf(qi.buf, q.inp, q.outp, q.size);
        let content2 = seq_of_buf(qi.buf, q.inp, (q.outp+1i32)%q.size, q.size);
        content1 == Seq_Cons {head: qi.buf[q.outp], tail: content2};
@*/
{
  /*@ unfold seq_of_buf(qi.buf, q.inp, q.outp, q.size); @*/
}

void prove_in_sync(struct queue *p)
/*@
requires take qi = QueueImpl(p);
         let q = qi.q;
ensures take qi_out = QueueImpl(p);
        qi == qi_out;
        cn_size(q.inp, q.outp, q.size) == length(qi.content);
@*/
{
  /*@ unfold seq_of_buf(qi.buf, q.inp, q.outp, q.size); @*/
  /*@ unfold length(seq_of_buf(qi.buf, q.inp, q.outp, q.size)); @*/
  /* if (((p->inp - p->outp + p->size) % p->size) == 0) { */
  /* } */
  /* else { */
  /*   Queue induction_step = *p; */
  /*   induction_step.outp = (induction_step.outp + 1) % induction_step.size; */
  /*   prove_in_sync(&induction_step); */
  /* } */
}


Queue *new(int n)
/*@ requires 0i32 < n;
             (i64) n + (i64) n + 2i64 < 2147483647i64;
    ensures take queue_out = QueueAbs(return);
            queue_out.size == n;
            queue_out.content == Seq_Nil {};
@*/
{
  int bufsize = n + 1;
  int *buff = malloc_buf(bufsize);
  Queue q = {0, 0, bufsize, buff};
  Queue *qptr = malloc_queue();
  *qptr = q;
  /*CN*/ prove_queue_empty(qptr);
  return qptr;
}

void put(Queue *q, int n)
/*@ requires take queue = QueueAbs(q);
             length(queue.content) < queue.size;
             let expected_content = snoc(queue.content, n);
    ensures take queue_out = QueueAbs(q);
            queue_out.content == expected_content;
            queue_out.size == queue.size;
@*/
{
  /*@ extract Owned<int>, q->inp; @*/
  /*CN*/ prove_buf_frame(q,n);
  q -> buf[q -> inp] = n;
  /*CN*/ prove_buf_cons(q);
  q -> inp = (q -> inp + 1) % q -> size;
}

int get(Queue *q)
/*@ requires take queue = QueueAbs(q);
             length(queue.content) > 1i32;
    ensures take queue_out = QueueAbs(q);
            return == hd(queue.content);
            queue_out.content == tl(queue.content);
            queue_out.size == queue.size;
@*/
{
  /*@ extract Owned<int>, q->outp; @*/
  /*CN*/ prove_in_sync(q);
  /*CN*/ prove_queue_get(q);
  int ans = q -> buf[q -> outp];
  q -> outp = (q -> outp + 1) % q -> size;
  return ans;
}

int queueSize(Queue *q)
/*@ requires take queue = QueueAbs(q);
    ensures take queue_out = QueueAbs(q);
            queue == queue_out;
            return == length(queue.content);
@*/
{
  /*CN*/ prove_in_sync(q);
  return (q->inp - q->outp + q->size) % q->size;
}

int main()
{
}