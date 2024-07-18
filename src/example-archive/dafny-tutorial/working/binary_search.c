// Binary search algorithm. The functional correctness of this algorithm depends
// on the array being sorted

int binary_search(int *a, int length, int value)
/*@ requires 
      let MAXi32 = (i64) 2147483647i64; // TODO: lift to library 

      0i32 <= length; 
      (2i64 * (i64) length) <= MAXi32; 
      take IndexPre = each (i32 j; 0i32 <= j && j < length)
                           {Owned<int>(a + j)}; @*/
/*@ ensures 
      take IndexPost = each (i32 j; 0i32 <= j && j < length)
                            {Owned<int>(a + j)}; 
      IndexPost == IndexPre; 
      (return < 0i32) || (IndexPost[return] == value); @*/
{
  int low = 0;
  int high = length;

  while (low < high)
  /*@ inv 
        {a}unchanged; {length}unchanged; {value}unchanged;  
        0i32 <= low; 
        low <= high; 
        high <= length; 
        ((i64) low + (i64) high) <= MAXi32; 
        take IndexInv = each (i32 j; 0i32 <= j && j < length)
                             {Owned<int>(a + j)}; 
        IndexInv == IndexPre; @*/
  {
    int mid = (low + high) / 2;
    /*@ extract Owned<int>, mid; @*/
    /*@ instantiate good<int>, mid;  @*/
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
