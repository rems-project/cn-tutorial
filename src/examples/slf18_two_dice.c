unsigned int val_rand (unsigned int n);
/*@ spec val_rand(u32 n);
    requires n > 0u32;
    ensures 0u32 <= return && return < n;
@*/

unsigned int two_dice ()
/*@ ensures 2u32 <= return && return <= 12u32; @*/
{
  unsigned int n1 = val_rand (6);
  unsigned int n2 = val_rand (6);
  unsigned int s = n1 + n2;
  return s + 2;
}
