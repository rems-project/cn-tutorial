#include <stddef.h>
#include "spec_funs.h"

/*@
// null-terminated strings with no extra buffer

predicate (datatype String) String_At(pointer p) {
    take h = RW<char>(p);
    take s = String_At_Aux(p, h);
    return s;
}

predicate (datatype String) String_At_Aux(pointer p, u8 h) {
    if (h == 0u8) {
        return String_Nil {};
    } else {
        take tl = String_At(array_shift<char>(p, 1u64));
        return String_Cons {head : h, tail : tl};
    }
}

// function [rec] (u64) string_len(String s) {
//   match s {
//     String_Nil {} => { 0u64 }
//     String_Cons { head : h , tail : tl } => { 1u64 + string_len(tl) }
//   }
// }

// function [rec] (datatype String) string_concat(String s1, String s2) {
//   match s1 {
//       String_Nil {} => { s2 }
//       String_Cons { head : h , tail : tl } => {
//       String_Cons { head : h, tail : string_concat(tl, s2) }
//       }
//   }
// }
@*/

// library functions with minimal buffer size arguments

extern size_t strlen(const char *s);
/*@ spec strlen(pointer s);
    requires
      take sIn = String_At(s);
    ensures
      take sOut = String_At(s);
      sIn == sOut;
      return == string_len(sIn);
@*/

extern char *strlcpy(char *dest, const char *src, size_t dest_size);
/*@ spec strlcpy(pointer dest, pointer src, u64 dest_size);
    requires
      take srcIn = String_At(src);
      take destIn = String_Buf_At(dest, dest_size);
      string_len(srcIn) < dest_size; // < to leave room for the null
    ensures
      take srcOut = String_At(src);
      take destOut = String_Buf_At(dest, dest_size);
      srcIn == srcOut;
      destOut == String_Buf { chars : srcIn, buf_len : dest_size };
      ptr_eq(return, dest);
@*/

extern int strcmp(char *s1, char *s2);
/*@ spec strcmp(pointer s1, pointer s2);
    requires
      take s1In = String_At(s1);
      take s2In = String_At(s2);
    ensures
      take s1Out = String_At(s1);
      take s2Out = String_At(s2);
      s1In == s1Out;
      s2In == s2Out;
      (return == 0i32) ? s1In == s2In : s1In != s2In;
@*/

extern char *strcat(char *dest, const char *src, size_t dest_size);
/*@ spec strcat(pointer dest, pointer src, u64 dest_size);
    requires
      take srcIn = String_At(src);
      take destIn = String_Buf_At(dest, dest_size);
      string_len(srcIn) + string_buf_len(destIn) < dest_size; // < to leave room for the null
    ensures
      take srcOut = String_At(src);
      take destOut = String_Buf_At(dest, dest_size);
      srcIn == srcOut;
      destOut == String_Buf { chars : string_concat(srcIn, chars(destIn)), buf_len : buf_len(destIn) };
@*/