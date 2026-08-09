return code: 1
./src/example-archive/SAW/broken/error-proof/00004.tutorial-dotprod.c:53:5: error: unexpected token after '}' and before 'ensures'
parsing "condition": seen "CN_TAKE LNAME VARIABLE EQ resource", expecting "SEMICOLON"
    ensures  take ax1 = each(u32 j; 0u32 <= j && j < size) { Owned<uint32_t>(array_shift<uint32_t>(x,j)) };
    ^~~~~~~ 
