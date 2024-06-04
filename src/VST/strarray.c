#include <stddef.h>
#include "hashfun.h"

/*@

predicate (datatype strf) Stringa (pointer p)
{
  take h = Owned<char>(p);
  take s = Stringa_Aux(p, h);
  //assert (h != 0u8 || s == Strf_E { } );
  return s;
}

predicate (datatype strf) Stringa_Aux (pointer p, u8 h)
{
  if (h == 0u8) {
    return Strf_E { };
  }
  else {
    assert (h != 0u8);
    take t = Stringa(array_shift<char>(p, 1u64));
    return Strf_NE { head : h, tail : t };
  }
}

predicate (datatype strf) StringaBlock(pointer p, u64 len) {
  assert (len >= 1u64); // required for null termination
  take s = each(u64 j; j < len) { Block<char>(array_shift<char>(p,j)) };
  assert (s[len - 1u64] == 0u8);
  return to_strf(s, len);
}

function (datatype strf) to_strf(map<u64, u8> s, u64 len) {
   to_strf_aux(s, len, 0u64)
}

function [rec] (datatype strf) to_strf_aux(map<u64, u8> s, u64 len, u64 offset) {
   if (len - offset <= 1u64) {
    // this is 1 because of the null termination
    Strf_E {}
   }
   else {
    Strf_NE { head : s[offset], tail : to_strf_aux(s, len, offset + 1u64)}
   }
}

@*/

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

/*@ lemma elems_owned (pointer s)
  requires
    take sIn = Stringa(s);
  ensures
    take sOut = each(u64 j; j <= strf_len(sIn)) { Owned<char>(array_shift<char>(s, j)) };
    each (u64 j; j < strf_len(sIn)) { sOut[j] != 0u8 };
    sOut[strf_len(sIn)] == 0u8;
@*/

/*@ lemma elems_owned_rev (pointer s, u64 len)
  requires
    take sIn = each(u64 j; j <= len) { Owned<char>(array_shift<char>(s, j)) };
    each (u64 j; j < len) { sIn[j] != 0u8 };
    sIn[len] == 0u8;
  ensures
    take sOut = Stringa(s);
    strf_len(sOut) == len;
@*/

// char str_get(char * s, size_t i) 
// /*@
// requires 
//   take sIn = Stringa(s);
//   i <= strf_len(sIn);
// ensures
//   take sOut = Stringa(s);
//   return == strf_get(sIn, i);
// @*/
// {
//   /*@ extract Owned<char>, i; @*/
//   return s[i];
// }