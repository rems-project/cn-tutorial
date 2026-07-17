#include <stddef.h>
#include "string_buf.c"

/*
Not used for current example, but potentially useful, including for `more_lemmas.broken.c`.
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

void sum_string_parts(char *s, size_t n)
/*@
requires
    take sIn = String_Buf_At(s, n);
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    string_len(sIn) + empty_buf_len(sIn) == buf_len(sIn);
@*/
{
    char c = s[0];
    if (c == '\0')
    {
        /*@ unfold string_len(sIn); @*/
        /*@ unfold empty_buf_len(sIn); @*/
        /*@ unfold buf_len(sIn); @*/
    }
    else
    {
        sum_string_parts(&s[1], n - (size_t)1);
        /*@ unfold string_len(sIn); @*/
        /*@ unfold empty_buf_len(sIn); @*/
        /*@ unfold buf_len(sIn); @*/
    }
}

/* Trusted lemmas */

/*@
lemma array_owned_shift_one_r(pointer s, u64 tail_owned_len) //TODO

requires
    take all = each (u64 i; i < 1u64 + tail_owned_len) {
        RW<char>(array_shift<char>(s, i))};
    tail_owned_len < MAXu64();
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
    tail_high < MAXu64();
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

/*@
lemma array_owned_shift_one_l(pointer s, u64 tail_owned_len)

requires
    take first = RW<char>(s);
    take rest = each (u64 i; i < tail_owned_len) {
        RW<char>(array_shift<char>(array_shift<char>(s, 1u64), i))};
    tail_owned_len < MAXu64();
ensures
    take all = each (u64 i; i < 1u64 + tail_owned_len) {
        RW<char>(array_shift<char>(s, i))};
@*/

/*@
lemma array_blocked_shift_one_l(pointer s, u64 tail_low, u64 tail_high) //TODO

requires
    take blockedIn = each (u64 i; tail_low < i && i < tail_high) {
        W<char>(array_shift<char>(array_shift<char>(s, 1u64), i))};
    tail_high < MAXu64();
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
    tail_buf_len < MAXu64();
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
lemma convert_to_write_only(pointer s, size_t n, size_t string_len, size_t index)

requires
    n >= 1u64;
    string_len < n;
    index <= string_len;
    take rwIn = each (u64 i; i <= string_len) {
        RW<char>(array_shift<char>(s, i)) };
    take wIn = each (u64 i; string_len < i && i < n) {
        W<char>(array_shift<char>(s, i)) };
ensures
    take rwOut = each (u64 i; i < index) {
        RW<char>(array_shift<char>(s, i)) };
    take wOut = each (u64 i; index <= i && i < n) {
        W<char>(array_shift<char>(s, i)) };
@*/