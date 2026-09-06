// Filed by @lwli11, see https://github.com/rems-project/cerberus/issues/856

#include <limits.h>

/*@  
lemma div(integer x, integer y)
  requires let b1 = 0 <= x && x <= MAXi32();
           let b2 = 0 <= y && y <= MAXi32();
  ensures (b1 && b2) implies (0 <= x / y && x / y <= MAXi32());

lemma mul_div(integer a, integer b, integer n)
  requires a > 0; b > 0; n > 0;
           a < n / b;
  ensures  0 < a*b; a*b < n;
@*/

int mult_timeout(int a, int b){
  /*@ apply div(MAXi32(),b); @*/
  if (a > 0 && b>0 && INT_MAX / b > a){
    /*@ apply mul_div(a,b,MAXi32()); @*/
    return a*b;
  }
  return 0;
}
