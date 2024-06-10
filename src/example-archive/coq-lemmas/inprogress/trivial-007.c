#include <stdbool.h>
/*@
  predicate (bool) MyCondition (u32 x){
    if (x > 4294967295u32){
      return false;
    } else {
      return true; 
    }
  } 

@*/

void trivial() 
{
  ; 
}
