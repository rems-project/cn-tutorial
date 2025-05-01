#include <stddef.h>
#include "spec_funs.h"

// /* NULL-TERMINATED STRING STANDARD LIBRARY FUNCTIONS */

extern char *malloc_str(size_t n);
/*@ spec malloc_str(size_t n);
    requires
      1u64 <= n; // 1 byte is required for null termination
    ensures
      take s = String_Buf_At(return, n);
@*/

extern void free_str(char *p, size_t n);
/*@ spec free_str(pointer p, u64 n);
    requires
      take s = String_Buf_At(p, n);
    ensures
      true;
@*/

// buffer version of strlen
extern size_t str_buf_len(const char *s, size_t n);
/*@ spec str_buf_len(pointer s, u64 n);
    requires
      take sIn = String_Buf_At(s, n);
    ensures
      take sOut = String_Buf_At(s, n);
      sIn == sOut;
      return == string_buf_len(sIn);
@*/

// buffer version of strcpy
extern char *str_buf_cpy(char *dest, const char *src, size_t dest_size, size_t src_size);
/*@ spec str_buf_cpy(pointer dest, pointer src, u64 dest_size, u64 src_size);
    requires
      take srcIn = String_Buf_At(src, src_size);
      take destIn = String_Buf_At(dest, dest_size);
      string_buf_len(srcIn) < dest_size; // < to leave room for the null
    ensures
      take srcOut = String_Buf_At(src, src_size);
      take destOut = String_Buf_At(dest, dest_size);
      srcIn == srcOut;
      destOut == String_Buf { chars : chars(srcIn), buf_len : dest_size };
      ptr_eq(return, dest);
@*/

// buffer version of strcmp; does not compare buffer size
extern int str_buf_cmp(char *s1, char *s2, size_t n1, size_t n2);
/*@ spec str_buf_cmp(pointer s1, pointer s2, u64 n1, u64 n2);
    requires
      take s1In = String_Buf_At(s1, n1);
      take s2In = String_Buf_At(s2, n2);
    ensures
      take s1Out = String_Buf_At(s1, n1);
      take s2Out = String_Buf_At(s2, n2);
      s1In == s1Out;
      s2In == s2Out;
      (return == 0i32) ? s1In == s2In : s1In != s2In;
@*/

// buffer version of strcat
extern char *str_buf_cat(char *dest, const char *src, size_t dest_size, size_t src_size);
/*@ spec str_buf_cat(pointer dest, pointer src, u64 dest_size, u64 src_size);
    requires
      take srcIn = String_Buf_At(src, src_size);
      take destIn = String_Buf_At(dest, dest_size);
      string_buf_len(srcIn) + string_buf_len(destIn) < dest_size; // < to leave room for the null
    ensures
      take srcOut = String_Buf_At(src, src_size);
      take destOut = String_Buf_At(dest, dest_size);
      srcIn == srcOut;
      destOut == String_Buf { chars : string_concat( chars(srcIn), chars(destIn)), buf_len : dest_size};
@*/