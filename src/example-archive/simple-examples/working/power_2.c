// Compute 2^1

/*@
lemma LemmaPowerUFDef(i32 y)
  requires 
    y >= 0i32; 
  ensures 
    (power_uf(2i32,0i32)) == 1i32; 
    (power_uf(2i32,y+1i32)) == (2i32 * power_uf(2i32,y)); 
@*/

int power_2()
/*@ ensures return == power_uf(2i32,1i32); @*/
{
  int i = 0;
  int pow = 1;
  pow = pow * 2;
  /*@ apply LemmaPowerUFDef(i);  @*/
  i = i + 1;
  return pow;
}
