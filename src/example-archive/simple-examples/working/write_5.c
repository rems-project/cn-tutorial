// Write into two locations that are adjacent in memory

void write_5(int *pair)
/*@ requires 
      take Cell1Pre = Owned(pair);
      take Cell2Pre = Owned(pair + 1i32); @*/
/*@ ensures 
      take Cell1Post = Owned(pair);
      take Cell2Post = Owned(pair + 1i32); 
      Cell1Post == 7i32; 
      Cell2Post == 8i32; @*/
{
  pair[0] = 7;
  pair[1] = 8;
}

// Same code, but specified using the `each` keyword

void write_5_alt(int *pair)
/*@ requires 
      take PairPre = each (i32 j; j == 0i32 || j == 1i32) {Owned(pair + j)}; @*/
/*@ ensures 
      take PairPost = each (i32 j; j == 0i32 || j == 1i32) {Owned(pair + j)}; 
      PairPost[0i32] == 7i32; 
      PairPost[1i32] == 8i32; 
      @*/
{
  /*@ extract Owned<int>, 0i32; @*/
  pair[0] = 7;
  /*@ extract Owned<int>, 1i32; @*/
  pair[1] = 8;
}
