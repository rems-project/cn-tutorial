// Swap the values stored in memory at *a and *b, via a temporary variable

void swap_1(int *a, int *b)
/*@ requires 
    take Pa = RW(a); 
    take Pb = RW(b); @*/
/*@ ensures 
    take Qa = RW(a);
    take Qb = RW(b);
    Qb == Pa;
    Qa == Pb; @*/
{
  int temp = *a;
  *a = *b;
  // *a = 0;  // <-- This would fail
  *b = temp;
}
