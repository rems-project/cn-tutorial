// Write into two locations that are adjacent in memory

void write_5(int *pair)
/*@ requires 
      take Cell1Pre = RW(pair);
      take Cell2Pre = RW(pair + 1i32);
    ensures 
      take Cell1Post = RW(pair);
      take Cell2Post = RW(pair + 1i32); 
      Cell1Post == 7i32; 
      Cell2Post == 8i32; @*/
{
  pair[0] = 7;
  pair[1] = 8;
}

// Same code, but specified using the `each` keyword

void write_5_alt(int *pair)
/*@ requires 
      take PairPre = each (i32 j; j == 0i32 || j == 1i32) {RW(pair + j)};
    ensures 
      take PairPost = each (i32 j; j == 0i32 || j == 1i32) {RW(pair + j)}; 
      PairPost[0i32] == 7i32; 
      PairPost[1i32] == 8i32; 
      @*/
{
  /*@ focus RW<int>, 0i32; @*/
  pair[0] = 7;
  /*@ focus RW<int>, 1i32; @*/
  pair[1] = 8;
}
