return code: 1
[1/3]: slnil -- pass
[2/3]: slcons -- pass
[3/3]: remove -- fail
./src/examples/dll/remove_orig.broken.c:9:9: error: Pointer `n` needs allocation ID
    if (n->prev != 0) {
        ~^~~~~~ 
(UB missing short message): UB_CERB004_unspecified__pointer_add
State file: file:///tmp/state__remove_orig.broken.c__remove.html
