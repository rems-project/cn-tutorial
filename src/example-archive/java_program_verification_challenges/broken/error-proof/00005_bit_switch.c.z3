return code: 1
[1/2]: select_mode -- fail
[2/2]: main -- pass
./src/example-archive/java_program_verification_challenges/broken/error-proof/00005_bit_switch.c:59:21: error: Missing resource for writing
                    mode = ACTION_ONE;
                    ~~~~~^~~ 
Resource needed: Block<unsigned ichar>(&mode)
State file: file:///tmp/state__00005_bit_switch.c__select_mode.html
