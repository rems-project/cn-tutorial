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
        len_lt_buf_size(&s[1], n - (size_t)1);
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
    /*@ split_case (c == 0u8); @*/
    string_len_not_max(&s[1], n - (size_t)1);
    len_lt_buf_size(&s[1], n - (size_t)1);
    plus_one_gt_zero(str_buf_len(&s[1], n - (size_t)1));
    one_plus_string_len(s, n);
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
        /*@ unfold string_len(s1In); @*/
        /*@ unfold string_len(s2In); @*/
        /*@ split_case (c2 == 0u8); @*/
        string_equal_impl_equal_len(&s1[1], n1 - (size_t)1, &s2[1], n2 - (size_t)1);
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
        nonzero_up_to_len(&s[1], n - (size_t)1);
        /*@ apply nonzero_up_to_len_step(s, n); @*/
    }
}

void update_empty_buf_preserves_string(char *s, size_t n, size_t new_empty_buf)
/*@
requires
    take sIn = String_Buf_At(s, n);
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    string_equal(sIn, update_empty_buf(sIn, new_empty_buf));
@*/
{
    char c = s[0];
    if (c == '\0')
    {
        /*@ unfold update_empty_buf(sIn, new_empty_buf); @*/
        /*@ unfold string_equal(sIn, update_empty_buf(sIn, new_empty_buf)); @*/
    }
    else
    {
        update_empty_buf_preserves_string(&s[1], n - (size_t)1, new_empty_buf);
        /*@ unfold update_empty_buf(sIn, new_empty_buf); @*/
        /*@ unfold string_equal(sIn, update_empty_buf(sIn, new_empty_buf)); @*/
    }
}

void update_empty_buf_preserves_len(char *s, size_t n, size_t new_empty_buf)
/*@
requires
    take sIn = String_Buf_At(s, n);
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    string_len(sIn) == string_len(update_empty_buf(sIn, new_empty_buf));
@*/
{
    char c = s[0];
    if (c == '\0')
    {
        /*@ unfold update_empty_buf(sIn, new_empty_buf); @*/
        /*@ unfold string_len(update_empty_buf(sIn, new_empty_buf)); @*/
        /*@ unfold string_len(sIn); @*/
    }
    else
    {
        update_empty_buf_preserves_len(&s[1], n - (size_t)1, new_empty_buf);
        /*@ unfold update_empty_buf(sIn, new_empty_buf); @*/
        /*@ unfold string_len(update_empty_buf(sIn, new_empty_buf)); @*/
        /*@ unfold string_len(sIn); @*/
    }
}

// void concat_nil_len(char *dest, char *src, size_t dest_size, size_t src_size)
// /*@
// requires
//     take srcIn = String_Buf_At(src, src_size);
//     take destIn = String_Buf_At(dest, dest_size);
//     is_nil_string_buf(destIn);
//     string_len(srcIn) + string_len(destIn) < dest_size;
// ensures
//     take srcOut = String_Buf_At(src, src_size);
//     take destOut = String_Buf_At(dest, dest_size);
//     srcIn == srcOut;
//     destIn == destOut;
//     string_len(string_buf_concat(destIn, srcIn)) == string_len(srcIn);
// @*/
// {
//     // char c = src[0];
//     // if (c == '\0')
//     // {
//     //     /*@ unfold string_len(srcIn); @*/
//     //     /*@ unfold string_len(destIn); @*/
//     //     /*@ unfold string_buf_concat(destIn, srcIn); @*/
//     //     /*@ unfold string_len(string_buf_concat(destIn, srcIn)); @*/
//     // }
//     // else
//     // {
//     //     nonempty_string_len(src, src_size);
//     //     /*@ unfold string_len(destIn); @*/
//     //     /*@ assert (dest_size > 1u64); @*/
//     //     concat_nil_len(&dest[1], &src[1], dest_size - (size_t)1, src_size - (size_t)1);
//     // }
// }

/*
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

        }*/

void concat_len(char *dest, char *src, size_t dest_size, size_t src_size)
/*@
requires
    take srcIn = String_Buf_At(src, src_size);
    take destIn = String_Buf_At(dest, dest_size);
    let len_sum = string_len(srcIn) + string_len(destIn);
    string_len(srcIn) + string_len(destIn) < dest_size;
ensures
    take srcOut = String_Buf_At(src, src_size);
    take destOut = String_Buf_At(dest, dest_size);
    srcIn == srcOut;
    destIn == destOut;
    string_len(string_buf_concat(destIn, srcIn)) == string_len(srcIn) + string_len(destIn);
@*/
{
    char c = dest[0];
    if (c == '\0')
    {
        update_empty_buf_preserves_len(src, src_size, dest_size - str_buf_len(src, src_size));
        /*@ unfold string_len(srcIn); @*/
        /*@ unfold string_len(destIn); @*/
        /*@ unfold string_buf_concat(destIn, srcIn); @*/
        /*@ unfold string_len(string_buf_concat(destIn, srcIn)); @*/
    }
    else
    {
        /*@ unfold string_len(destIn); @*/
        concat_len(&dest[1], src, dest_size - (size_t)1, src_size);
        /*@ unfold string_len(srcIn); @*/
        /*@ unfold string_buf_concat(destIn, srcIn); @*/
        /*@ unfold string_len(string_buf_concat(destIn, srcIn)); @*/
    }
}