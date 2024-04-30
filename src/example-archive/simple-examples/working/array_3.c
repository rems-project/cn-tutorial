// Writes 7 into all positions in an array of size n. The proof establishes that
// the whole array is written to 7. This is an example of how quantification
// works over pure values.

void array_3(int *arr, int n)
/*@ requires 
      0i32 < n;
      take arrayStart = each (i32 j; 0i32 <= j && j < n) {Owned<int>(arr + j)}; @*/
/*@ ensures 
      take arrayEnd = each (i32 j; 0i32 <= j && j < n) {Owned<int>(arr + j)};
      each (i32 j; 0i32 <= j && j < n) {arrayEnd[j] == 7i32}; @*/
{
  int i = 0;
  while (i < n)
  /*@ inv {n}unchanged; 
          {arr}unchanged;
          0i32 <= i; 
          i <= n;
          take arrayInv = each (i32 j; 0i32 <= j && j < n) {Owned<int>(arr + j)};
          each (i32 j; 0i32 <= j && j < i) {arrayInv[j] == 7i32}; @*/ 
  {
    /*@ extract Owned<int>, i; @*/
    *(arr + i) = 7;
    i++;
  };
  return;
}
