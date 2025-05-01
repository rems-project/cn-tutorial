#include "cn_types.h"

/*@
function (datatype String) chars(String_Buf s) {
    match s {
        String_Buf { chars : cs, buf_len : n } => { cs }
    }
}

function (u64) buf_len(String_Buf s) {
    match s {
        String_Buf { chars : cs, buf_len : n } => { n }
    }
}

function [rec] (u64) string_len(String s) {
    match s {
      String_Nil {} => { 0u64 }
      String_Cons { head : h , tail : tl } => { 1u64 + string_len(tl) }
    }
}

function [rec] (u64) string_buf_len(String_Buf sb) {
    match sb {
      String_Buf { chars : cs, buf_len : n } => { string_len(cs) }
    }
}

function [rec] (datatype String) string_concat(String s1, String s2) {
    match s1 {
        String_Nil {} => { s2 }
        String_Cons { head : h , tail : tl } => {
        String_Cons { head : h, tail : string_concat(tl, s2) }
        }
    }
}

// defaults to \0
function [rec] (u8) string_nth(String s, u64 n) {
    match s {
        String_Nil {} => { 0u8 }
        String_Cons { head : h , tail : tl } => {
            n == 0u64 ? h : string_nth(tl, n - 1u64)
        }
    }
}

function [rec] (u8) string_buf_nth(String_Buf sb, u64 n) {
    match sb {
        String_Buf { chars : cs, buf_len : n0 } => { string_nth(cs, n) }
    }
}
@*/