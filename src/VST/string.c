#include <stddef.h>
#include "string_util.c"

/* CORE OWNERSHIP PREDICATES FOR STRINGS */

/*@
predicate (datatype strf) Stringa(pointer p)
{
  take h = Owned<char>(p);
  take s = Stringa_Aux(p, h);
  assert (h != 0u8 || s == Strf_E { } );
  return s;
}

predicate (datatype strf) Stringa_Aux (pointer p, u8 h)
{
  if (h == 0u8) {
    return Strf_E { };
  }
  else {
    take t = Stringa(array_shift<char>(p, 1u64));
    return Strf_NE { head : h, tail : t };
  }
}

// TODO: returning a strf acts like it's initialized
predicate (datatype strf) StringaBlock(pointer p, u64 len) {
  assert (len >= 1u64); // required for null termination
  take s = each(u64 j; j < len) { Block<char>(array_shift<char>(p,j)) };
  assert (s[len - 1u64] == 0u8);
  return to_strf(s, len);
}
@*/





/* STRING LIB FUNCTIONS */

extern char * malloc_str(size_t n);
/*@ spec malloc_str(u64 n);
    requires 
      1u64 <= n; // 1 is required for null termination
    ensures 
      take s = StringaBlock(return, n);
@*/

extern void free_str(char * p, size_t n);
/*@ spec free_str(pointer p, u64 n);
    requires 
      take s = StringaBlock(p, n);
    ensures 
      true;
@*/

extern size_t strlen(const char *s); 
/*@ spec strlen(pointer s);
    requires 
      take sfIn = Stringa(s);
    ensures 
      take sfOut = Stringa(s);
      sfIn == sfOut;
      return == strf_len(sfIn);
@*/

extern char *strcpy(char *dest, const char *src);
/*@ spec strcpy(pointer dest, pointer src);
    requires
      take srcIn = Stringa(src);
      take destIn = StringaBlock(dest, strf_len(srcIn) + 1u64);
    ensures
      take destOut = Stringa(dest);
      take srcOut = Stringa(src);
      srcIn == srcOut;
      destOut == srcIn;
@*/

extern int strcmp(char * str1, char * str2);
/*@ spec strcmp(pointer str1, pointer str2);
    requires 
      take str1In = Stringa(str1);
      take str2In = Stringa(str2);
    ensures
      take str1Out = Stringa(str1);
      take str2Out = Stringa(str2);
      str1In == str1Out;
      str2In == str2Out;
      (return == 0i32) ? str1In == str2In : str1In != str2In;
@*/

extern int strcat(char * str1, char * str2);
/*@ spec strcmp(pointer str1, pointer str2);
    requires 
      take str1In = Stringa(str1);
      take str2In = Stringa(str2);
      // TODO: requirement about buffer lengths
    ensures
      take str1Out = Stringa(str1);
      take str2Out = Stringa(str2);
      str1Out = strf_concat(str1In, str2In);
      str2Out = str2In;
@*/





/* LEMMAS */

// CONVERTING CHAR ARRAYS TO STRINGS
// void array_to_rec(char* s, unsigned int len)
// /*@ 
//   requires
//     let len64 = (u64) len;
//     take sIn = each(u64 j; j <= len64) { Owned<char>(array_shift<char>(s, j)) };
//     each (u64 j; j < len64) { sIn[j] != 0u8 };
//     sIn[len64] == 0u8;
//   ensures
//     take sOut = Stringa(s);
//     strf_len(sOut) == len64;
// @*/
// {
//   /*@ extract Owned<char>, 0u64; @*/
//   char c = s[0];
//   if (c == 0) {
//     /*@ assert (each (u64 j; j < len64) { sIn[j] != 0u8 }); @*/
//     /*@ assert (sIn[0u64] == 0u8); @*/
//     /*@ assert (0u64 == len64 || sIn[0u64] != 0u8); @*/
//     /*@ assert (len64 == 0u64); @*/
//     return;
//   } else {
//     array_to_rec(s++, len - 1);
//     return;
//   }
// }

// // CONVERTING STRINGS TO CHAR ARRAYS
// void rec_to_array(char* s)
// /*@ 
//   requires
//     take sIn = Stringa(s);
//   ensures
//     take sOut = each(u64 j; j <= strf_len(sIn)) { Owned<char>(array_shift<char>(s, j)) };
//     each (u64 j; j < strf_len(sIn)) { sOut[j] != 0u8 };
//     sOut[strf_len(sIn)] == 0u8;
// @*/
// {
//   char c = s[0];
//   if (c == 0) {
//     /*@ unfold strf_len(sIn); @*/
//     /*@ split_case (c == 0u8); @*/
//     return;
//   } else {
//     rec_to_array(s++);
//     return;
//   }
// }





/* BACKWARDS STRING SEGMENTS FOR ITERATION REASONING */

/*@

predicate (datatype str_seg_back) Str_Seg_Back(pointer s, u64 len) {
  if (len == 0u64) {
    return StrSegBack_E { };
  }
  else {
    take h = Owned<char>(s);
    take tl = Str_Seg_Back(array_shift<char>(s, -1i64), len - 1u64);
    return StrSegBack_NE { tail : tl, head: h };
  }
}

@*/
