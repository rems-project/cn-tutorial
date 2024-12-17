return code: 1
[1/5]: generic_m -- fail
[2/5]: C_m -- pass
[3/5]: Inheritance_m -- pass
[4/5]: Inheritance_test -- fail
[5/5]: main -- pass
./src/example-archive/java_program_verification_challenges/inprogress/00009_inheritance.c:76:20: error: Pointer `instance.object` needs allocation ID
            return ((C*)instance.object)->m(instance);
                   ~~~~~~~~~~~~~~~~~~~~~^~~ 
(UB missing short message): UB_CERB004_unspecified__pointer_add
State file: file:///tmp/state__00009_inheritance.c__generic_m.html
./src/example-archive/java_program_verification_challenges/inprogress/00009_inheritance.c:99:16: error: Pointer `instance.object` needs allocation ID
        return ((Inheritance*)instance.object)->base.m(instance);
               ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^~~~~~ 
(UB missing short message): UB_CERB004_unspecified__pointer_add
State file: file:///tmp/state__00009_inheritance.c__Inheritance_test.html
