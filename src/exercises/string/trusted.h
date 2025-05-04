#include "string_buf.c"

/*
Trusted string lemmas.
*/

/*@
lemma array_owned_shift_one_l(pointer s, u64 tail_owned_len) //TODO

requires
    take first = RW<char>(s);
    take rest = each (u64 i; i < tail_owned_len) {
        RW<char>(array_shift<char>(array_shift<char>(s, 1u64), i))};
    tail_owned_len < 18446744073709551615u64;
ensures
    take all = each (u64 i; i < 1u64 + tail_owned_len) {
        RW<char>(array_shift<char>(s, i))};
@*/

/*@
lemma array_blocked_shift_one_l(pointer s, u64 tail_low, u64 tail_high) //TODO

requires
    take blockedIn = each (u64 i; tail_low < i && i < tail_high) {
        W<char>(array_shift<char>(array_shift<char>(s, 1u64), i))};
    tail_high < 18446744073709551615u64;
ensures
    take blockedOut = each (u64 i; tail_low + 1u64 < i && i < 1u64 + tail_high) {
        W<char>(array_shift<char>(s, i))};
@*/

/*@
lemma array_shift_one_r(pointer s, size_t tail_string_len, size_t tail_buf_len)

requires
    take ownedIn = each (u64 i; i < 1u64 + tail_string_len) {
        RW<char>(array_shift<char>(s, i))};
    take blockedIn = each (u64 i; tail_string_len + 1u64 < i && i < 1u64 + tail_buf_len) {
        W<char>(array_shift<char>(s, i))};
    tail_string_len < tail_buf_len;
    tail_buf_len < 18446744073709551615u64;
    take nullIn = RW<char>(array_shift<char>(s, 1u64 + tail_string_len));
    nullIn == 0u8;
    each (u64 i; i < 1u64 + tail_string_len) {
        ownedIn[i] != 0u8
    };
ensures
    take first = RW<char>(s);
    first != 0u8;
    take ownedOut = each (u64 i; i < tail_string_len) {
        RW<char>(array_shift<char>(array_shift<char>(s, 1u64), i))};
    take blockedOut = each (u64 i; tail_string_len < i && i < tail_buf_len) {
        W<char>(array_shift<char>(array_shift<char>(s, 1u64), i))};
    take nullOut = RW<char>(array_shift<char>(array_shift<char>(s, 1u64), tail_string_len));
    nullOut == 0u8;
    each (u64 i; i < tail_string_len) {
        ownedOut[i] != 0u8
    };
@*/

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
lemma nonzero_up_to_len_step(pointer s, size_t n)

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