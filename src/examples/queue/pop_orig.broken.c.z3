return code: 1
[1/1]: pop_queue -- fail
./src/examples/queue/pop_orig.broken.c:5:26: error: Pointer `q` needs allocation ID
  struct queue_cell* h = q->front;
                         ~^~~~~~~ 
(UB missing short message): UB_CERB004_unspecified__pointer_add
State file: file:///tmp/state__pop_orig.broken.c__pop_queue.html
