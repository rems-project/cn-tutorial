#include <stddef.h>
#include "string_buf.c"

/*
In progress CN versions of trusted lemmas.
*/

void array_to_string_buf_c(char *s, size_t string_len, size_t n)
/*@
requires
    take sArray = each(u64 i; i < string_len) {
        RW<char>( array_shift<char>(s, i) ) };
    take sRem = each(u64 i; string_len < i && i < n) {
        W<char>( array_shift<char>(s, i)) };
    n >= 1u64;
    string_len < n;
    take sNull = RW<char>(array_shift<char>(s, string_len));
    sNull == 0u8;
    // we need some "fix arbitrary i" tactic for the below
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
{
    /*@ split_case (string_len == 0u64); @*/
    /*@ focus RW<char>, 0u64; @*/
    char c = s[0];
    /*@split_case (c == 0u8); @*/
    if (string_len == (unsigned long long)0)
    {
        if (c == '\0')
        {
            /*@ unfold string_len(String_Buf_Nil { empty_buf : n }); @*/
        }
        else
        {
            // impossible
            /*@ instantiate 0u64; @*/
            /*@ assert (false); @*/
        }
    }
    else
    {
        /*@ apply array_shift_one_r(s, string_len - 1u64, n - 1u64); @*/
        array_to_string_buf_c(&s[1], string_len - (unsigned long long)1, n - (unsigned long long)1);
        one_plus_string_len(s, n);
    }
}

void string_buf_to_array_c(char *s, size_t n)
/*@
requires
    take sBuf = String_Buf_At(s, n);
ensures
    string_len(sBuf) < n;
    n >= 1u64;
    take sArray = each (u64 i; i < string_len(sBuf)) {
        RW<char>( array_shift<char>(s, i) ) };
    take sRem = each (u64 i; string_len(sBuf) < i && i < n) {
        W<char>( array_shift<char>(s, i) ) };
    // we need some "fix arbitrary i" tactic for the below
    each (u64 i; i < string_len(sBuf)) {
        string_buf_nth(sBuf, i) == sArray[i]
    };
    take sNull = RW<char>(array_shift<char>(s, string_len(sBuf)));
    sNull == 0u8;
@*/
{
    char c = s[0];
    if (c == '\0')
    {
        /*@ unfold string_len(sBuf); @*/
    }
    else
    {
        char c1 = s[1];
        string_buf_to_array_c(&s[1], n - (unsigned long long)1);
        /*@ unfold string_len(sBuf); @*/
        /*@ apply array_owned_shift_one_l(s, string_len(sBuf) - 1u64); @*/
        /*@ apply array_blocked_shift_one_l(s, string_len(sBuf) - 1u64, n - 1u64); @*/
    }
}

/*
In progress potentially-useful functions.
*/

// edit any character in the initial string to a non-null character
void edit_at(char *s, size_t buf_len, size_t index, char c)
/*@
requires
    take sIn = String_Buf_At(s, buf_len);
    index < string_len(sIn);
    c != 0u8;
ensures
    take sOut = String_Buf_At(s, buf_len);
    // we need some "fix arbitrary i" tactic for the below
    each (u64 i; i < string_len(sOut)) {
        i == index
            ? string_buf_nth(sOut, i) == c
            : string_buf_nth(sOut, i) == string_buf_nth(sIn, i)
    };
@*/
{
    size_t sLen = str_buf_len(s, buf_len);
    /*@ apply string_buf_to_array(s, buf_len, string_len(sIn)); @*/
    edit_array_at(s, sLen, index, c);
    /*@ instantiate index; @*/
    /*@ apply array_to_string_buf(s, buf_len, sLen); @*/
}

// allocate a string of size n and set the first byte to '\0'
char *init_string(size_t n)
/*@
requires
    1u64 <= n; // 1 byte is required for null termination
ensures
    take sOut = String_Buf_At(return, n);
    sOut == String_Buf_Nil { empty_buf : n };
@*/
{
    char *s = malloc_str(n);
    /*@ apply string_buf_to@*/
    s[0] = '\0';
    return s;
}
