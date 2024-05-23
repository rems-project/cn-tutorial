#include <stddef.h>

extern void exit(int n);
/*@ spec exit(i32 n);
    requires true;
    ensures false;
@*/

/*@
function (i64) i32max() {
    2147483647i64
}

function (i64) i32min() {
    -2147483648i64
}

function (u64) u32max() {
    4294967295u64
}

@*/

extern unsigned int modu32 (unsigned int a, unsigned int b); //TODO
/*@
spec modu32(u32 a, u32 b);
requires
    b != 0u32;
ensures
    return == mod(a,b);
@*/