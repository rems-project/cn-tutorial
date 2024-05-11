// Example of the `cn_function` feature for extracting spec-level functions.
// This example extracts a ternary bitwise-OR 

// Give the CN-level signature for bitwise-OR 
/*@
function (i32) bw_or(i32 x, i32 y)
@*/

// Define bitwise-OR in code
int c_bw_or(int x, int y)
// Lift the bitwise-OR function to a specification function 
/*@ cn_function bw_or; @*/
/*@ ensures return == bw_or(x,y); @*/  // <-- Trivial, should hold by construction 
{
  return x | y;
}

int cn_function_1(int x, int y)
/*@ ensures return == bw_or(x,y); @*/
{
  // L-R switch x / y. Requires that CN proves bw_or is symmetrical 
  return y | x; 
}

