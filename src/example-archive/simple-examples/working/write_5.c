// Write into two locations that are adjacent in memory

void write_5(int *pair)
/*@ requires 
      take Cell1Pre = RW(pair);
      take Cell2Pre = RW(pair + 1);
    ensures 
      take Cell1Post = RW(pair);
      take Cell2Post = RW(pair + 1); 
      Cell1Post == 7; 
      Cell2Post == 8; @*/
{
  pair[0] = 7;
  pair[1] = 8;
}

// Same code, but specified using the `each` keyword

void write_5_alt(int *pair)
/*@ requires 
      take PairPre = each (integer j; j == 0 || j == 1) {RW(pair + j)};
    ensures 
      take PairPost = each (integer j; j == 0 || j == 1) {RW(pair + j)}; 
      PairPost[0] == 7; 
      PairPost[1] == 8; 
      @*/
{
  /*@ focus RW<int>, 0; @*/
  pair[0] = 7;
  /*@ focus RW<int>, 1; @*/
  pair[1] = 8;
}
