// Example of the `cn_function` feature for extracting spec-level functions 

// Give the CN-level signature for bitwise-OR 
/*@
function (integer) bw_or_tern(integer x, integer y, integer z)
@*/

// Define bitwise-OR in code
int c_bw_or_tern(int x, int y, int z)
// Lift the bitwise-OR function to a specification function 
/*@ cn_function bw_or_tern;
    ensures return == bw_or_tern(x,y,z); @*/  // <-- Trivial, should hold by construction 
{
  return x | (y | z);
}

int cn_function_2(int x, int y, int z)
/*@ ensures return == bw_or_tern(x,y,z); @*/
{
  // Permute x,y,z. Requires commutativity / symmetry properties 
  return (z | x) | y; 
}
