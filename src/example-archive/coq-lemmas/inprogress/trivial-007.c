#include <stdbool.h>
/*@
  predicate (bool) MyCondition (u32 x){
    if (x > 4294967295u32){
      return false;
    } else {
      return true; 
    }
  } 
  
  lemma lem_bit_wise_or (u32 x)
  requires MyCondition(x) == true;
  ensures true;
@*/

void trivial() 
{
  ; 
}
