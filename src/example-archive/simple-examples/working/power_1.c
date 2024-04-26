// Calculate 2^0, and establish the post-condition using the uninterpreted
// function `power_uf`. We need a lemma to allow CN to reason about this
// function.

// Variant 1 - define the lemma as a function call without a body, using the
// `trusted` keyword. The important properties are 
//   1. the base case - power_uf(2,0) = 1 
//   2. the inductive case - power(2,y+1) == 2 * power_uf(2,y)

void lemma_power_uf_def(int y)
/*@ trusted @*/
/*@ requires y >= 0i32 @*/
/*@ ensures 
      (power_uf(2i32,0i32)) == 1i32; 
      (power_uf(2i32,y+1i32)) == (2i32 * power_uf(2i32,y)) @*/
{}

int power_1()
/*@ ensures return == power_uf(2i32,0i32) @*/
{
  int i = 0;
  int pow = 1;
  lemma_power_uf_def(i);
  return pow;
}

// Variant 2 - define the lemma at the specification level 

/*@
lemma LemmaPowerUFDef(i32 y)
  requires 
    y >= 0i32
  ensures 
    (power_uf(2i32,0i32)) == 1i32; 
    (power_uf(2i32,y+1i32)) == (2i32 * power_uf(2i32,y))
@*/

int power_1_alt()
/*@ ensures return == power_uf(2i32,0i32) @*/
{
  int i = 0;
  int pow = 1;
  /*@ apply LemmaPowerUFDef(i); @*/
  return pow;
}
