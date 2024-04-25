// Writes 7 into a given offset in an array 

void array_1(int *arr, int size, int off)
/*@ requires 
      take arrayStart = each (i32 j; 0i32 <= j && j < size) {Owned(arr + j)}; 
      0i32 <= off; 
      off < size @*/
/*@ ensures take arrayEnd = each (i32 j; 0i32 <= j && j < size) {Owned(arr + j)} @*/
{
  int i = off;
  /*@ extract Owned<int>, i; @*/  // <-- required to read / write
  arr[off] = 7;
  i++;
  return;
}
