#include <stdlib.h>

typedef struct queue
{
  int inp;
  int outp;
  int size;
  int *buf;
} Queue;

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

Queue *new(int n)
{
  int bufsize = n;
  int *buff = malloc_buf(bufsize);
  Queue q = {0, 0, bufsize, buff};
  Queue *qptr = malloc_queue();
  *qptr = q;
  return qptr;
}

void put(Queue *q, int n)
{
  q->buf[q->inp] = n;
  q->inp = (q->inp + 1) % q->size;
}

int get(Queue *q)
{
  int ans = q->buf[q->outp];
  q->outp = (q->outp + 1) % q->size;
  return ans;
}

int size(Queue *q)
{
  return (q->inp - q->outp) % q->size;
}

int main()
{
}
