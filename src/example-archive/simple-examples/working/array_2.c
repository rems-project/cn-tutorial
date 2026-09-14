// Read from a given offset into an array, then write 7 into the same offset

int array_2(int *arr, int size, int off)
/*@ requires 
      take arrayStart = each (integer j; 0  <= j && j < size) {RW(arr + j)};
      0 <= off; 
      off < size; 
      arrayStart[off] != 0;
    ensures  
      take arrayEnd = each (integer j; 0  <= j && j < size) {RW(arr + j)};
      arrayEnd[off] == 7; 
      return == arrayStart[off]; @*/
{
  /*@ focus RW<int>, off; @*/
  /*@ instantiate off; @*/
 int tmp = arr[off];
  arr[off] = 7;
  return tmp; 
}

int main(void) {
  int arr[5] = {1, 4, 6, 9, 10};
  array_2(arr, 5, 3);
}