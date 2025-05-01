#include "util.c"

void simple_ex(char *s, unsigned long long n)
/*@
    requires
        take sIn = String_Buf_At(s, n);
        n < 3u64;
    ensures
        true;
@*/
{
    char *sb = malloc_str(5);
    unsigned long long m = str_buf_len(sb, 5);
    // m == 0

    /*@ apply len_lt_buf_size(s, n); @*/
    sb = str_buf_cpy(sb, s, 5, n);

    m = str_buf_len(sb, 5);
    // m == n

    int j = str_buf_cmp(s, sb, n, 5);
    // j == 0

    /*@ apply string_buf_to_array(s, n); @*/
    /*@ focus RW<char>, 0u64; @*/
    write(s, n, 0, 'c');
    /*@ apply array_to_string_buf(s, n); @*/
    /*@ apply string_buf_to_array(sb, 5u64); @*/
    /*@ focus RW<char>, 0u64; @*/
    write(sb, 5, 0, 'g');
    /*@ apply array_to_string_buf(sb, 5u64); @*/

    j = str_buf_cmp(s, sb, n, 5);
    // j != 0

    /*@
    unfold string_buf_len(sIn);
    assert (string_buf_len(sIn) <= 1u64);
    @*/
    sb = str_buf_cat(sb, s, 5, n);
    m = str_buf_len(sb, 5);
    // m == 2 * n

    free_str(sb, 5);
    free_str(s, n);
}

// parser and printer of pairs of numbers