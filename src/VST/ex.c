#include "strarray.c"

void bad (char* s)
/*@
requires
    take sIn = Stringa(s);
ensures
    take sOut = Stringa(s);
    sIn == sOut;
@*/
{
    char c = s[0];
    /*@ assert (c != 0u8 || sIn == Strf_E { } ); @*/
}

void hack (char* s)
/*@
requires
  take sIn = Stringa(s);
ensures
  take sOut = Stringa(s);
  sIn == sOut;
@*/
{
    char c = s[0];
    if (c == 0) {
        /*@ assert (c != 0u8 || sIn == Strf_E { } ); @*/
    }
}