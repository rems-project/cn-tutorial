#include "string_buf.c"

/*
Trusted string lemmas.
*/

/*@
lemma array_to_string_buf(pointer s, u64 n, u64 string_len)
requires
    take sArray = each(u64 i; i < string_len) {
        RW<char>( array_shift<char>(s, i) ) };
    take sRem = each(u64 i; string_len < i && i < n) {
        W<char>( array_shift<char>(s, i)) };
    n >= 1u64;
    string_len < n;
    take sNull = RW<char>(array_shift<char>(s, string_len));
    sNull == 0u8;
    each (u64 i; i < string_len) {
        sArray[i] != 0u8
    };
ensures
    take sBuf = String_Buf_At(s, n);
    string_len == string_len(sBuf);
    each (u64 i; i < string_len(sBuf)) {
        string_buf_nth(sBuf, i) == sArray[i]
    };
@*/

/*@
lemma string_buf_to_array(pointer s, u64 n, u64 string_len) //TODO
requires
    take sBuf = String_Buf_At(s, n);
    string_len(sBuf) == string_len;
ensures
    string_len < n;
    n >= 1u64;
    take sArray = each (u64 i; i < string_len) {
        RW<char>( array_shift<char>(s, i) ) };
    take sRem = each (u64 i; string_len < i && i < n) {
        W<char>( array_shift<char>(s, i) ) };
    each (u64 i; i < string_len) {
        string_buf_nth(sBuf, i) == sArray[i]
    };
    take sNull = RW<char>(array_shift<char>(s, string_len));
    sNull == 0u8;
@*/

/*@
lemma nonzero_up_to_len_step(pointer s, u64 n)

requires
    n > 1u64;
    take sHead = RW<char>(s);
    take sTail = String_Buf_At(array_shift<char>(s, 1u64), n - 1u64);
    each (u64 i; i < string_len(sTail)) {
        string_buf_nth(sTail, i) != 0u8 };
ensures
    take sOut = String_Buf_At(s, n);
    sOut == String_Buf_Cons { head : sHead, tail : sTail };
    each (u64 i; i < string_len(sOut)) {
        string_buf_nth(sOut, i) != 0u8 };
@*/