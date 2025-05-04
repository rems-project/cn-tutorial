#include <stddef.h>
#include "string_buf.c"

/*
Not used for current example, but potentially useful.
*/

/* CN lemmas */

// buffer size for a nonempty string is > 1
void nonempty_buf_size(char *s, size_t n)
/*@
requires
    take sIn = String_Buf_At(s, n);
    !is_nil_string_buf(sIn);
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    n > 1u64;
@*/
{
    char c = s[0];
    /*@ split_case (c == 0u8); @*/
}

// empty string has length 0
void nil_string_len(char *s, size_t n)
/*@
requires
    take sIn = String_Buf_At(s, n);
    is_nil_string_buf(sIn);
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    string_len(sOut) == 0u64;
@*/
{
    /*@ unfold string_len(sIn); @*/
}

/* Trusted lemmas */

/*@
lemma array_owned_shift_one_r(pointer s, u64 tail_owned_len) //TODO

requires
    take all = each (u64 i; i < 1u64 + tail_owned_len) {
        RW<char>(array_shift<char>(s, i))};
    tail_owned_len < 18446744073709551615u64;
ensures
    take first = RW<char>(s);
    take rest = each (u64 i; i < tail_owned_len) {
        RW<char>(array_shift<char>(array_shift<char>(s, 1u64), i))};
@*/

/*@
lemma array_blocked_shift_one_r(pointer s, u64 tail_low, u64 tail_high) //TODO

requires
    take blockedIn = each (u64 i; tail_low + 1u64 < i && i < 1u64 + tail_high) {
        W<char>(array_shift<char>(s, i))};
    tail_high < 18446744073709551615u64;
ensures
    take blockedOut = each (u64 i; tail_low < i && i < tail_high) {
        W<char>(array_shift<char>(array_shift<char>(s, 1u64), i))};
@*/

/*@
lemma nonzero_shift_one_r(pointer s, size_t tail_len)

requires
    take sIn = each (u64 i; i < 1u64 + tail_len) {
        RW<char>(array_shift<char>(s, i))};
    each (u64 i; i < 1u64 + tail_len) {
        sIn[i] != 0u8
    };
ensures
    take sOut = each (u64 i; i < 1u64 + tail_len) {
        RW<char>(array_shift<char>(s, i))};
    each (u64 i; i < tail_len) {
        sOut[1u64 + i] != 0u8
    };
@*/