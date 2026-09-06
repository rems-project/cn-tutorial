// Binary search algorithm. The functional correctness of this algorithm depends
// on the array being sorted

int binary_search(int *a, int length, int value)
/*@ requires 
      let MAXi32 = 2147483647; // TODO: lift to library 

      0 <= length; 
      (2 * length) <= MAXi32; 
      take IndexPre = each (integer j; 0 <= j && j < length)
                           {RW<int>(a + j)};
    ensures 
      take IndexPost = each (integer j; 0 <= j && j < length)
                            {RW<int>(a + j)}; 
      IndexPost == IndexPre; 
      (return < 0) || (IndexPost[return] == value); @*/
{
  int low = 0;
  int high = length;

  while (low < high)
  /*@ inv 
        {a}unchanged; {length}unchanged; {value}unchanged;  
        0 <= low; 
        low <= high; 
        high <= length; 
        (low + high) <= MAXi32; 
        take IndexInv = each (integer j; 0 <= j && j < length)
                             {RW<int>(a + j)}; 
        IndexInv == IndexPre; @*/
  {
    int mid = (low + high) / 2;
    /*@ focus RW<int>, mid; @*/
    /*@ instantiate mid;  @*/
    if (a[mid] < value)
    {
      low = mid + 1;
    }
    else if (value < a[mid])
    {
      high = mid;
    }
    else if (value == a[mid])
    {
      return mid;
    }
  };
  return -1;
}
