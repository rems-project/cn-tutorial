/*@ function [rec] (u32) my_spec(u32 n) { 42u32 } @*/

unsigned int factorial(unsigned int n)
/*@ ensures return == my_spec(n); @*/
{
  /*@ unfold my_spec(n); @*/
  return 42;
}
