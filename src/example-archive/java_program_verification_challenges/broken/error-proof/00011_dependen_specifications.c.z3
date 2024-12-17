return code: 1
[1/3]: iabs -- fail
[2/3]: isqrt -- fail
[3/3]: main -- pass
./src/example-archive/java_program_verification_challenges/broken/error-proof/00011_dependen_specifications.c:52:23: error: Undefined behaviour
    if (x < 0) return -x;
                      ^~ 
an exceptional condition occurs during the evaluation of an expression (§6.5#5)
State file: file:///tmp/state__00011_dependen_specifications.c__iabs.html
./src/example-archive/java_program_verification_challenges/broken/error-proof/00011_dependen_specifications.c:76:5: error: Unprovable constraint
    while (sum <= x)
    ^~~~~~~~~~~~~~~~ 
Constraint from ./src/example-archive/java_program_verification_challenges/broken/error-proof/00011_dependen_specifications.c:81:6:
	    sum <= x + 2i32 *count+1i32; 
	    ^~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
State file: file:///tmp/state__00011_dependen_specifications.c__isqrt.html
