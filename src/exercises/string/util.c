#include "string_buf.c"

// UTILITIES

void nonempty_buf_size(char *s, size_t n)
/*@
requires
    take sIn = String_Buf_At(s, n);
    chars(sIn) != String_Nil{};
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    n > 1u64;
@*/
{
    char c = s[0];
    /*@ split_case (c == 0u8); @*/
}

void len_lt_buf_size(char *s, size_t n)
/*@
requires
    take sIn = String_Buf_At(s, n);
ensures
    take sOut = String_Buf_At(s, n);
    sIn == sOut;
    string_buf_len(sOut) < n;
@*/
{
    char c = s[0];

    if (c == '\0')
    {
        /*@ unfold string_buf_len(String_Buf {buf_len: n, chars: String_Nil {}}); @*/
        /*@ unfold string_len(String_Nil{});@*/
    }
    else
    {
        char c1 = s[1];
        nonempty_buf_size(s, n);
        len_lt_buf_size(&c1, n - (unsigned long long)1);
    }
}