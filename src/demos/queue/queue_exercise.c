#include <stdlib.h>

/*@
// copying from list_cn_types.h
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}
@*/

#include "../../examples/list_hdtl.h"


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

function (i32) size (i32 inp, i32 outp, i32 bufsize)
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
  && (0i32 <= inp && inp < bufsize)
  && (0i32 <= outp && outp < bufsize)
}

predicate {datatype seq content, i32 size} QueueP (pointer p) {
  take q = Owned<Queue>(p);
  take buf = each (i32 i; 0i32 <= i && i < q.size) { Owned<int>(q.buf + i) };
  assert (queue_wf (q.inp, q.outp, q.size));
  let content = seq_of_buf(buf, q.inp, q.outp, q.size);
  let size = size(q.inp, q.outp, q.size);
  assert(length(content) == size);
  return {content: content, size: q.size - 1i32};
}

//for proof purposes only
predicate {Queue q, map<i32,i32> buf} Queue_ImplP(pointer p)
{
  take q = Owned<Queue>(p);
  take buf = each (i32 i; 0i32 <= i && i < q.size) { Owned<int>(q.buf + i) };
  assert (queue_wf (q.inp, q.outp, q.size));
  return {q: q, buf: buf} ;
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
requires take qi = Queue_ImplP(p);
         size(qi.q.inp, qi.q.outp, qi.q.size) == 0i32;
ensures take qi_out = Queue_ImplP(p);
        qi == qi_out;
        seq_of_buf(qi.buf, qi.q.inp, qi.q.outp, qi.q.size) == Seq_Nil {};
@*/
{
  /*@ unfold seq_of_buf(qi.buf, qi.q.inp, qi.q.outp, qi.q.size); @*/
}

// for proof
void prove_queue_put(struct queue *p, int n)
/*@
requires take qi = Queue_ImplP(p);
         let q = qi.q;
         size(q.inp, q.outp, q.size) < q.size;
ensures take qi_out = Queue_ImplP(p);
        qi == qi_out;
        let content_before = seq_of_buf(qi.buf, q.inp, q.outp, q.size);
        let content_after = seq_of_buf(qi.buf[q.inp: n], (q.inp+1i32)%q.size, q.outp, q.size);
        content_after == Seq_Cons {head: n, tail: content_before};
@*/
{
  /*@ unfold seq_of_buf(qi.buf[q.inp: n + 0i32], (q.inp+1i32)%q.size, q.outp, q.size); @*/
}

// for proof
void prove_queue_get(struct queue *p)
/*@
requires take qi = Queue_ImplP(p);
         let q = qi.q;
         size(q.inp, q.outp, q.size) > 1i32;
ensures take qi_out = Queue_ImplP(p);
        qi == qi_out;
        let content1 = seq_of_buf(qi.buf, q.inp, q.outp, q.size);
        let content2 = seq_of_buf(qi.buf, q.inp, (q.outp+1i32)%q.size, q.size);
        content1 == Seq_Cons {head: qi.buf[q.outp], tail: content2};
@*/
{
  /*@ unfold seq_of_buf(qi.buf, q.inp, q.outp, q.size); @*/
}



Queue *new(int n)
/*@ requires 0i32 < n && n < 2147483647i32;
    ensures take queue_out = QueueP(return);
            queue_out.size == n;
            queue_out.content == Seq_Nil {};
@*/
{
  int bufsize = n+1;
  int *buff = malloc_buf(bufsize);
  Queue q = {0, 0, bufsize, buff};
  Queue *qptr = malloc_queue();
  *qptr = q;
  /*CN*/ prove_queue_empty(qptr);
  /*@ unfold length(Seq_Nil {}); @*/
  return qptr;
}

void put(Queue *q, int n)
/*@ requires take queue = QueueP(q);
             length(queue.content) < queue.size;
             let expected_content = Seq_Cons{head: n, tail: queue.content};
    ensures take queue_out = QueueP(q);
            queue_out.content == expected_content;
            queue_out.size == queue.size;
@*/
{
  /*CN*/ prove_queue_put(q,n);
  /*@ extract Owned<int>, q->inp; @*/
  /*@ unfold length (expected_content); @*/
  q->buf[q->inp] = n;
  q->inp = (q->inp + 1) % q->size;
}

int get(Queue *q)
/*@ requires take queue = QueueP(q);
             length(queue.content) > 1i32;
    ensures take queue_out = QueueP(q);
            return == hd(queue.content);
            queue_out.content == tl(queue.content);
            queue_out.size == queue.size;
@*/
{
  /*@ extract Owned<int>, q->outp; @*/
  /*CN*/ prove_queue_get(q);
  int ans = q->buf[q->outp];
  q->outp = (q->outp + 1) % q->size;
  // unfold length(queue.content); 
  return ans;
}

int size(Queue *q)
/*@ requires take queue = QueueP(q);
    ensures take queue_out = QueueP(q);
            queue == queue_out;
            return == length(queue.content);
@*/
{
  return ((q->inp - q->outp) + q->size) % q->size;
}

int main()
{
}
