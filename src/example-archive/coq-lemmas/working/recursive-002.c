// Fails to export becasue of recursive definition

/*@
function [rec] (u32) fib_spec(u32 n)
{
  if (n <= 0u32) {
    1u32
  } else {
    if (n == 1u32) {
      1u32
    } else {
      fib_spec(n - 1u32) + fib_spec(n - 2u32)
    }
  }
}
@*/


/*@
lemma fib_lemma (u32 n)
  requires true;
  ensures fib_spec(n) == fib_spec(n - 1u32) + fib_spec(n - 2u32);
@*/

// Function to calculate the factorial of a number
unsigned int fibonacci(unsigned int n)
/*@ requires 0u32 <= n; n <= 4294967294u32;  @*/
/*@ requires fib_spec(n) < 4294967295u32; @*/
/*@ ensures return == fib_spec(n); @*/
{
    if (n <= 1) {
      /*@ unfold fib_spec(n); @*/
      return 1; // Return 1
    }

    unsigned previous = 1;
    unsigned tmp = 1;
    unsigned result = 1;
    
    /*@ unfold fib_spec(1u32-1u32); @*/
    /*@ unfold fib_spec(1u32); @*/
    for (unsigned int i = 1; i < n; i++)
      /*@ inv {n}unchanged; @*/
      /*@ inv 0u32 < n; i <= n; @*/
      /*@ inv 0u32 < i; @*/
      /*@ inv previous == fib_spec(i-1u32); @*/
      /*@ inv result == fib_spec(i); @*/
      {
	tmp = previous;
	previous = result;
	result = tmp + previous;
	/*@ apply fib_lemma(i+1u32); @*/
      }

    return result;
}
