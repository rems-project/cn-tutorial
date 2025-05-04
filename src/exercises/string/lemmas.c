#include <stddef.h>
#include "trusted.h"

/*
String lemmas proven in CN.
*/

// string length is less than buffer size
void len_lt_buf_size(char *s, size_t n)
/*@
requires
    take sIn = String_Buf_At(s, n);
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    string_len(sOut) < n;
@*/
{
    char c = s[0];

    if (c == '\0')
    {
        /*@ unfold string_len(sIn); @*/
    }
    else
    {
        len_lt_buf_size(&s[1], n - (unsigned long long)1);
        /*@ unfold string_len(sIn);@*/
    }
}

// nonempty string's length is 1 + its tail's length
void one_plus_string_len(char *s, size_t n)
/*@
requires
    take sIn = String_Buf_At(s, n);
    !is_nil_string_buf(sIn);
ensures
    take h = RW<char>(s);
    take tl = String_Buf_At(array_shift<char>(s, 1u64), n - 1u64);
    sIn == String_Buf_Cons { head : h, tail : tl };
    string_len(sIn) == 1u64 + string_len(tl);
@*/
{
    char c = s[0];
    /*@ split_case (c == 0u8); @*/
    /*@ unfold string_len(sIn); @*/
}

// string length is less than max u64
void string_len_not_max(char *s, size_t n)
/*@
requires
    take sIn = String_Buf_At(s, n);
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    string_len(sIn) < 18446744073709551615u64;
@*/
{
    len_lt_buf_size(s, n);
}

// adding one to less than max u64 does not wrap around
void plus_one_gt_zero(size_t n)
/*@
requires
    n < 18446744073709551615u64;
ensures
    1u64 + n > 0u64;
@*/
{
}

// length of nonempty string is > 0
void nonempty_string_len(char *s, size_t n)
/*@
requires
    take sIn = String_Buf_At(s, n);
    !is_nil_string_buf(sIn);
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    string_len(sIn) > 0u64;
@*/
{
    char c = s[0];
    if (c == '\0')
    {
        /* impossible */
        /*@ assert (false); @*/
    }
    else
    {
        string_len_not_max(&s[1], n - (unsigned long long)1);
        len_lt_buf_size(&s[1], n - (unsigned long long)1);
        plus_one_gt_zero(str_buf_len(&s[1], n - (unsigned long long)1));
        one_plus_string_len(s, n);
    }
}

// equal strings have the same length
void string_equal_impl_equal_len(char *s1, size_t n1, char *s2, size_t n2)
/*@
requires
    take s1In = String_Buf_At(s1, n1);
    take s2In = String_Buf_At(s2, n2);
    string_equal(s1In, s2In);
ensures
    take s1Out = String_Buf_At(s1, n1);
    take s2Out = String_Buf_At(s2, n2);
    s1In == s1Out;
    s2In == s2Out;
    string_len(s1In) == string_len(s2In);
@*/
{
    char c1 = s1[0];
    char c2 = s2[0];
    if (c1 == '\0')
    {
        /*@ unfold string_equal(s1In, s2In); @*/
        /*@ unfold string_len(s1In); @*/
        /*@ unfold string_len(s2In); @*/
    }
    else
    {
        /*@ unfold string_equal(s1In, s2In); @*/
        /*@ split_case (c2 == 0u8); @*/
        /*@ unfold string_len(s1In); @*/
        /*@ unfold string_len(s2In); @*/
        string_equal_impl_equal_len(&s1[1], n1 - (unsigned long long)1, &s2[1], n2 - (unsigned long long)1);
    }
}

// all elements of a string are nonzero up to (excluding) string_len
void nonzero_up_to_len(char *s, size_t n)
/*@
requires
    take sIn = String_Buf_At(s, n);
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    each (u64 i; i < string_len(sIn)) {
        string_buf_nth(sIn, i) != 0u8 };
@*/
{
    char c = s[0];
    if (c == '\0')
    {
        /*@ unfold string_len(sIn); @*/
    }
    else
    {
        /*@ unfold string_buf_nth(sIn, 0u64); @*/
        nonzero_up_to_len(&s[1], n - (unsigned long long)1);
        /*@ apply nonzero_up_to_len_step(s, n); @*/
    }
}