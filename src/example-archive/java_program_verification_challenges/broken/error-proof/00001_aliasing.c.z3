return code: 1
[1/3]: createC -- fail
[2/3]: m -- fail
[3/3]: main -- pass
./src/example-archive/java_program_verification_challenges/broken/error-proof/00001_aliasing.c:18:17: error: Unknown function 'malloc_proxy'
    C* c = (C*) malloc(sizeof(C)); // Allocate memory for C
                ^~~~~~ 
./src/example-archive/java_program_verification_challenges/broken/error-proof/00001_aliasing.c:36:5: error: Pointer `call_createC0.return` needs allocation ID
    c->a = c;         // Alias to itself
    ~^~~ 
(UB missing short message): UB_CERB004_unspecified__pointer_add
State file: file:///tmp/state__00001_aliasing.c__m.html
