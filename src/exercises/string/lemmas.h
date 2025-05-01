#include "util.c"

/*@
// conversion to and from arrays

lemma array_to_string_buf(pointer s, size_t n)
    requires
        take sArray = each(u64 i; i < n) {
            RW<char>( array_shift<char>(s, i)) };
    ensures
        take sBuf = String_Buf_At(s, n);
        each (u64 i; i < string_buf_len(sBuf)) {
            string_buf_nth(sBuf, i) == sArray[i]
        };

lemma string_buf_to_array(pointer s, size_t n)
    requires
        take sBuf = String_Buf_At(s, n);
    ensures
        take sArray = each(u64 i; i < n) {
            RW<char>( array_shift<char>(s, i)) };
        each (u64 i; i < string_buf_len(sBuf)) {
            string_buf_nth(sBuf, i) == sArray[i]
        };

@*/

/*@
// length lemmas

lemma len_lt_buf_size (pointer s, size_t n)
    requires
        take sIn = String_Buf_At(s, n);
    ensures
        take sOut = String_Buf_At(s, n);
        sIn == sOut;
        match sOut {
            String_Buf { chars : cs, buf_len : n0 } => {
                (string_buf_len(sOut) < n0) && (n == n0)
            }
        };

lemma lt_len_impl_nonzero (pointer s, size_t n)
    requires
        take sBuf = String_Buf_At(s, n);
    ensures
        take sArray = each(u64 i; i < n) {
            RW<char>( array_shift<char>(s, i)) };
        each (u64 i; i < string_buf_len(sBuf)) {
            string_buf_nth(sBuf, i) == sArray[i]
        };
        each (u64 i; i < string_buf_len(sBuf)) {
            sArray[i] != 0u8
        };


@*/
