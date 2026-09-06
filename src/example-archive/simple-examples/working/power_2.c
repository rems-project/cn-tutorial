// Compute 2^1

/*@ function (integer) power_uf(integer x, integer y) @*/


/*@
lemma LemmaPowerUFDef(integer y)
  requires 
    y >= 0; 
  ensures 
    (power_uf(2,0)) == 1; 
    (power_uf(2,y+1)) == (2 * power_uf(2,y)); 
@*/

int power_2()
/*@ ensures return == power_uf(2,1); @*/
{
  int i = 0;
  int pow = 1;
  pow = pow * 2;
  /*@ apply LemmaPowerUFDef(i);  @*/
  i = i + 1;
  return pow;
}
