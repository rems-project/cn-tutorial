// Compute 2^y 
// TODO: fix this 

/*@
lemma LemmaPowerUFDef(i32 y)
  requires 
    y >= 0i32
  ensures 
    (power_uf(2i32,0i32)) == 1i32; 
    (power_uf(2i32,y+1i32)) == (2i32 * power_uf(2i32,y))
@*/

int power2_3(int y)
/*@ requires 0i32 < y; y <= 32i32 @*/
/*@ ensures return == power_uf(2i32,y) @*/
{
    int i = 0;
    int pow = 1;
    /*@ apply LemmaPowerUFDef(i); @*/

    while (i < y)
    /*@ inv 0i32 <= i; i <= y;
            inv 0i32 <= y; y <= 32i32;
            pow == power_uf(2i32,i);
            inv 0i32 < pow; 
            pow < power(2i32,32i32) @*/
    {
        pow = pow * 2;
        /*@ apply LemmaPowerUFDef(i); @*/
        i = i + 1;
    };

    return pow;
}
