#include "cn_types.h"

/*
Logical string functions for use in specifications.
*/

/*@
// the length of the *entire* buffer, including the string
function [rec] (u64) buf_len(String_Buf s) {
    match s {
        String_Buf_Nil { empty_buf : n } => { n }
        String_Buf_Cons { head : h, tail : tl } => { 1u64 + buf_len(tl) }
    }
}

// the length of just the string
function [rec] (u64) string_len(String_Buf s) {
    match s {
      String_Buf_Nil { empty_buf : n } => { 0u64 }
      String_Buf_Cons { head : h , tail : tl } => { 1u64 + string_len(tl) }
    }
}

// the length of the buffer space *after* the string, including the null
function [rec] (u64) empty_buf_len(String_Buf s) {
    match s {
        String_Buf_Nil { empty_buf : n } => { n }
        String_Buf_Cons { head : h, tail : tl } => { empty_buf_len(tl) }
    }
}

// updates the number of empty bytes
function [rec] (datatype String_Buf) update_empty_buf(String_Buf s, u64 new_empty_buf)
{
    match s {
        String_Buf_Nil { empty_buf : nDest } => { String_Buf_Nil { empty_buf : new_empty_buf } }
        String_Buf_Cons { head : h, tail : tl } => {
            String_Buf_Cons { head : h, tail : update_empty_buf(tl, new_empty_buf) }
        }
    }
}

// in-place string concat
// assumes destination buffer has enough space for source string
function [rec] (datatype String_Buf) string_buf_concat(String_Buf dest, String_Buf src) {
    match dest {
        String_Buf_Nil { empty_buf : nDest } => {
            // string_len(src) should be strictly less than nDest
            update_empty_buf(src, nDest - string_len(src))
        }
        String_Buf_Cons { head : h , tail : tl } => {
            String_Buf_Cons { head : h, tail : string_buf_concat(tl, src) }
        }
    }
}

// defaults to \0
function [rec] (u8) string_buf_nth(String_Buf s, u64 n) {
    match s {
        String_Buf_Nil { empty_buf : nS } => { 0u8 }
        String_Buf_Cons { head : h , tail : tl } => {
            n == 0u64 ? h : string_buf_nth(tl, n - 1u64)
        }
    }
}

// checks if input buffer represents the empty string
function (boolean) is_nil_string_buf(String_Buf s) {
    match s {
        String_Buf_Nil {empty_buf : n } => { true }
        String_Buf_Cons { head : h , tail : tl } => { false }
    }
}

// compares strings contained in two buffers; does not compare buffer size
function [rec] (boolean) string_equal(String_Buf s1, String_Buf s2) {
    match s1 {
        String_Buf_Nil { empty_buf : n1 } => {
            match s2 {
                String_Buf_Nil { empty_buf : n2 } => { true }
                String_Buf_Cons { head : h2, tail : tl2 } => { false }
            }
        }
        String_Buf_Cons { head : h1, tail : tl1 } => {
            match s2 {
                String_Buf_Nil { empty_buf : n2 } => { false }
                String_Buf_Cons { head : h2, tail : tl2 } => {
                    h1 == h2 && string_equal(tl1, tl2)
                }
            }
        }
    }
}

@*/