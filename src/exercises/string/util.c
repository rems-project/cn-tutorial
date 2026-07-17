#include <stddef.h>
#include "lemmas.c"

/*
Library functions for null-terminated strings.
*/

// edit any character up to (not including) string_len
void edit_array_at(char *s, size_t string_len, size_t index, char c)
/*@
requires
    take sIn = each (u64 i; i < string_len) {
            RW<char>(array_shift(s, i))
        };
    take sNullIn = RW<char>(array_shift(s, string_len));
    index < string_len;
ensures
    take sOut = each (u64 i; i < string_len) {
        RW<char>(array_shift(s, i))
    };
    each (u64 i; i < string_len) {
        i == index
            ? sOut[i] == c
            : sOut[i] == sIn[i]
    };
    take sNullOut = RW<char>(array_shift(s, string_len));
    sNullOut == sNullIn;
@*/
{
    /*@ focus RW<char>, index; @*/
    s[index] = c;
}