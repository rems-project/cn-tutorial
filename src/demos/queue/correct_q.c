#include <stdlib.h>

typedef struct queue
{ int inp;
  int outp;
  int size;
  int *buf;
} Queue;

Queue *new(int n)
{ int bufsize = n + 1;
  int *buff = malloc(bufsize*sizeof(int));
  Queue q = {0,0,bufsize,buff};
  Queue *qptr = malloc(sizeof(Queue));
  *qptr = q;
  return qptr;
}

void put(Queue *q, int n)
{ q -> buf[q -> inp] = n;
  q -> inp = (q -> inp + 1) % q -> size;
}

int get(Queue *q)
{ int ans = q -> buf[q -> outp];
  q -> outp = (q -> outp + 1) % q -> size;
  return ans;
}

int size(Queue *q)
{ return (q->inp - q->outp + q->size) % q -> size;
}

