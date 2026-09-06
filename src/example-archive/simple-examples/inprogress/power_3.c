// Compute 2^y 
// TODO: fix this 

/*@
lemma LemmaPowerUFDef(integer i)
  requires 
    0 <= i
  ensures 
    power_uf(2,0) == 1; 
    power_uf(2,i+1) == (power_uf(2,i) * 2)
@*/

/*@
lemma LemmaPowerOrd(integer i, integer j)
  requires
    0 <= i;
    i < j
  ensures 
    (power_uf(2, i) * 2) <= power_uf(2,j)
@*/

int power2_3(int y)
/*@ requires 
      let MAXi32 = 2147483647; 
      0 < y; 
      power_uf(2,y) <= MAXi32 @*/
/*@ ensures return == power_uf(2,y) @*/
{
    int i = 0;
    int pow = 1;
    /*@ apply LemmaPowerUFDef(i); @*/

    while (i < y)
    /*@ inv 0 <= i; i <= y;
            {y}unchanged; 
            pow == power_uf(2,i) @*/
    {
        /*@ apply LemmaPowerUFDef(i); @*/
        /*@ apply LemmaPowerOrd(i,y); @*/
        pow = pow * 2;
        i = i + 1;
    };

    return pow;
}
