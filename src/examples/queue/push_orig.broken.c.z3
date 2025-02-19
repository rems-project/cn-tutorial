return code: 1
[1/1]: push_queue -- fail
./src/examples/queue/push_orig.broken.c:8:7: error: Pointer `q` needs allocation ID
  if (q->back == 0) {
      ~^~~~~~ 
(UB missing short message): UB_CERB004_unspecified__pointer_add
State file: file:///tmp/state__push_orig.broken.c__push_queue.html
