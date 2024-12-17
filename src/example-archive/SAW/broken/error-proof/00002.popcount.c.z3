return code: 1
[1/3]: pop_count -- pass
[2/3]: pop_count_mul -- pass
[3/3]: pop_count_sparse -- fail
./src/example-archive/SAW/broken/error-proof/00002.popcount.c:66:13: error: Undefined behaviour
        n = n + 1;
            ~~^~~ 
an exceptional condition occurs during the evaluation of an expression (§6.5#5)
State file: file:///tmp/state__00002.popcount.c__pop_count_sparse.html
