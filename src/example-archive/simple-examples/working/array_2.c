// Read from a given offset into an array, then write 7 into the same offset

int array_2(int *arr, int size, int off)
/*@ requires 
      take arrayStart = each (i32 j; 0i32  <= j && j < size) {RW(arr + j)};
      0i32 <= off; 
      off < size; 
      arrayStart[off] != 0i32; @*/
/*@ ensures  
      take arrayEnd = each (i32 j; 0i32  <= j && j < size) {RW(arr + j)};
      arrayEnd[off] == 7i32; 
      return == arrayStart[off]; @*/
{
  /*@ focus RW<int>, off; @*/
  int tmp = arr[off];
  arr[off] = 7;
  return tmp; 
}
