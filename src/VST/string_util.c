#include "hashfun.h"

// FUNCTION FOR CONVERTING A LOGICAL CHARACTER ARRAY TO A LOGICAL STRING
/*@
function (datatype strf) to_strf(map<u64, u8> s, u64 len) {
   to_strf_aux(s, len, 0u64)
}

function [rec] (datatype strf) to_strf_aux(map<u64, u8> s, u64 len, u64 offset) {
   if (len - offset <= 1u64) {
    // this is 1 because of the null termination
    Strf_E {}
   }
   else {
    Strf_NE { head : s[offset], tail : to_strf_aux(s, len, offset + 1u64)}
   }
}
@*/