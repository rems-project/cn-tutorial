// Swap the values stored in memory at *a and *b, via a temporary variable

void swap_1(int *a, int *b)
/*@ requires 
    take Pa = Owned(a); 
    take Pb = Owned(b) @*/
/*@ ensures 
    take Qa = Owned(a);
    take Qb = Owned(b);
    Qb == Pa;
    Qa == Pb @*/
{
  int temp = *a;
  *a = *b;
  // *a = 0;  // <-- This would fail
  *b = temp;
}
