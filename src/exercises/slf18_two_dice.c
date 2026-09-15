unsigned int val_rand (unsigned int n);
/*@ spec val_rand(integer n);
    requires n > 0;
    ensures 0 <= return && return < n;
@*/

unsigned int two_dice ()
/*@ ensures 2 <= return && return <= 12; @*/
{
  unsigned int n1 = val_rand (6);
  unsigned int n2 = val_rand (6);
  unsigned int s = n1 + n2;
  return s + 2;
}
