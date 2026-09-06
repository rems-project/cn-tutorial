// A linear search algorithm

int linear_search(int *a, int length, int key)
/*@ requires 
      0 < length; 
      take IndexPre = each (integer j; 0 <= j && j < length)
                           {RW<int>(a + j)};
    ensures 
      take IndexPost = each (integer j; 0 <= j && j < length)
                            {RW<int>(a + j)};
      (return < 0) || (IndexPost[return] == key); 
      each (integer j; 0 <= j && j < length) 
           {return >= 0 || IndexPre[j] != key}; 
      IndexPre == IndexPost; @*/
{
  int idx = 0;

  while (idx < length)
  /*@ inv 
        {a}unchanged; {length}unchanged; {key}unchanged; 
        0 <= idx; 
        idx <= length; 
        take IndexInv = each (integer j; 0 <= j && j < length)
                             {RW<int>(a + j)}; 
        IndexInv == IndexPre; 
        each (integer j; 0 <= j && j < idx) {IndexPre[j] != key}; @*/
  {
    /*@ focus RW<int>, idx; @*/
    /*@ instantiate idx; @*/
    if (*(a + idx) == key)
    {
      return idx;
    }
    idx = idx + 1;
  };
  idx = -1;
  return idx;
}

