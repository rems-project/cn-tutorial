// Compute 2^y 
// TODO: fix this 

/*@
lemma LemmaPowerUFDef(i32 i)
  requires 
    0i32 <= i
  ensures 
    power_uf(2i32,0i32) == 1i32; 
    power_uf(2i32,i+1i32) == (power_uf(2i32,i) * 2i32)
@*/

/*@
lemma LemmaPowerOrd(i32 i, i32 j)
  requires
    0i32 <= i;
    i < j
  ensures 
    (power_uf(2i32, i) * 2i32) <= power_uf(2i32,j)
@*/

int power2_3(int y)
/*@ requires 
      let MAXi32 = 2147483647i64; 
      0i32 < y; 
      (i64) power_uf(2i32,y) <= MAXi32 @*/
/*@ ensures return == power_uf(2i32,y) @*/
{
    int i = 0;
    int pow = 1;
    /*@ apply LemmaPowerUFDef(i); @*/

    while (i < y)
    /*@ inv 0i32 <= i; i <= y;
            {y}unchanged; 
            pow == power_uf(2i32,i) @*/
    {
        /*@ apply LemmaPowerUFDef(i); @*/
        /*@ apply LemmaPowerOrd(i,y); @*/
        pow = pow * 2;
        i = i + 1;
    };

    return pow;
}
