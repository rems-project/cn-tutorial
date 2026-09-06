// Writes 7 into all positions in an array of size n. The proof establishes that
// the whole array is written to 7. This is an example of how quantification
// works over pure values.

void array_3(int *arr, int n)
/*@ requires 
      0 < n;
      take arrayStart = each (integer j; 0 <= j && j < n) {RW<int>(arr + j)};
    ensures 
      take arrayEnd = each (integer j; 0 <= j && j < n) {RW<int>(arr + j)};
      each (integer j; 0 <= j && j < n) {arrayEnd[j] == 7}; @*/
{
  int i = 0;
  while (i < n)
  /*@ inv {n}unchanged; 
          {arr}unchanged;
          0 <= i; 
          i <= n;
          take arrayInv = each (integer j; 0 <= j && j < n) {RW<int>(arr + j)};
          each (integer j; 0 <= j && j < i) {arrayInv[j] == 7}; @*/ 
  {
    /*@ focus RW<int>, i; @*/
    *(arr + i) = 7;
    i++;
  };
  return;
}
