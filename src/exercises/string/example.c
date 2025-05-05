#include "util.c"

/*
Example using string library functions.
*/

void simple_ex(char *s1, size_t n1, size_t n2, char c1, char c2)
/*@
    requires
        take sIn = String_Buf_At(s1, n1);
        !is_nil_string_buf(sIn);
        (u128) string_len(sIn) + (u128) string_len(sIn) < (u128) n2; // so it fits in allocated buffer twice
        // string_len(sIn) < 9223372036854775808u64; // n1 + n1 < maximum u64
        c1 != c2;
        c1 != 0u8;
        c2 != 0u8;
    ensures
        true;
@*/
{
    // allocate second string
    char *s2 = malloc_str(n2);

    // copy s1 into s2
    s2 = str_buf_cpy(s2, s1, n2, n1);

    // compare s1 and s2
    int j = str_buf_cmp(s1, s2, n1, n2);
    /*@ assert (j == 0i64); @*/

    // edit s1
    size_t s1Len = str_buf_len(s1, n1);
    size_t s2Len = str_buf_len(s2, n2);
    nonzero_up_to_len(s1, n1);
    nonempty_string_len(s1, n1);
    string_equal_impl_equal_len(s1, n1, s2, n2);
    /*@ apply string_buf_to_array(s1, n1, s1Len); @*/
    edit_array_at(s1, s1Len, 0, c1);
    /*@ apply array_to_string_buf(s1, n1, s1Len); @*/

    // edit s2 differently
    s2Len = str_buf_len(s2, n2);
    nonzero_up_to_len(s2, n2);
    /*@ apply string_buf_to_array(s2, n2, s2Len); @*/
    edit_array_at(s2, s2Len, 0, c2);
    /*@ apply array_to_string_buf(s2, n2, s2Len); @*/

    s2 = str_buf_cat(s2, s1, n2, n1);

    free_str(s1, n1);
    free_str(s2, n2);
}