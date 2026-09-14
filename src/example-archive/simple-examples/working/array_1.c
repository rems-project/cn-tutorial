// Writes 7 into a given offset in an array 

void array_1(int *arr, int size, int off)
/*@ requires 
      take arrayStart = each (integer j; 0 <= j && j < size) {RW(arr + j)}; 
      0 <= off; 
      off < size;
    ensures take arrayEnd = each (integer j; 0 <= j && j < size) {RW(arr + j)}; @*/
{
  int i = off;
  /*@ focus RW<int>, i; @*/  // <-- required to read / write
  arr[off] = 7;
  i++;
  return;
}

int main(void) {
  int arr[5] = {1, 4, 6, 9, 10};
  array_1(arr, 5, 3);
}