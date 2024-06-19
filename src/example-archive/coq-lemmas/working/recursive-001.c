/*@
function [rec] (u32) fact_spec(u32 n)
{
  if (n <= 0u32) { 1u32 }
  else { n * fact_spec(n - 1u32) }
}
@*/


/*@
lemma spec_lemma (u32 n)
  requires true;
  ensures fact_spec(n) == n * fact_spec(n-1u32);
@*/

// Function to calculate the factorial of a number
unsigned int factorial(unsigned int n)
/*@ requires 0u32 <= n; n <= 4294967294u32;  @*/
/*@ requires fact_spec(n) < 4294967295u32; @*/
/*@ ensures return == fact_spec(n); @*/
{
    if (n <= 0) {
      /*@ unfold fact_spec(n); @*/
      return 1; // Return 1
    }

    unsigned result = 1;
    /*@ unfold fact_spec(1u32-1u32); @*/
    for (unsigned int i = 1; i <= n; i++)
      /*@ inv {n}unchanged; @*/
      /*@ inv 0u32 < n; i <= n+1u32; @*/
      /*@ inv 0u32 < i; @*/
      /*@ inv result == fact_spec(i-1u32); @*/
      {
        result *= i;
	/*@ apply spec_lemma((i+1u32)-1u32); @*/
      }

    return result;
}
