// A linear search algorithm

int linear_search(int *a, int length, int key)
/*@ requires 
      0i32 < length; 
      take IndexPre = each (i32 j; 0i32 <= j && j < length)
                           {Owned<int>(a + j)}; @*/
/*@ ensures 
      take IndexPost = each (i32 j; 0i32 <= j && j < length)
                            {Owned<int>(a + j)};
      (return < 0i32) || (IndexPost[return] == key); 
      each (i32 j; 0i32 <= j && j < length) 
           {return >= 0i32 || IndexPre[j] != key}; 
      IndexPre == IndexPost; @*/
{
  int idx = 0;

  while (idx < length)
  /*@ inv 
        {a}unchanged; {length}unchanged; {key}unchanged; 
        0i32 <= idx; 
        idx <= length; 
        take IndexInv = each (i32 j; 0i32 <= j && j < length)
                             {Owned<int>(a + j)}; 
        IndexInv == IndexPre; 
        each (i32 j; 0i32 <= j && j < idx) {IndexPre[j] != key}; @*/
  {
    /*@ extract Owned<int>, idx; @*/
    if (*(a + idx) == key)
    {
      return idx;
    }
    idx = idx + 1;
  };
  idx = -1;
  return idx;
}

