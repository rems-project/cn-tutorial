// Take as input two values, x and y, and the address of a struct. Add x and y
// together and store in the struct's fst field, then subtract y from x and
// store in the struct's snd field

struct int_pair
{
  int fst;
  int snd;
};

void multiple_returns(int x, int y, struct int_pair *ret)
/*@ requires 
      let MAXi32 = (i64) 2147483647i64; 
      let MINi32 = (i64) -2147483647i64;

      take PairPre = RW<struct int_pair>(ret);
      MINi32 <= (i64) x + (i64) y; 
      (i64) x + (i64) y <= MAXi32;
      MINi32 <= (i64) x - (i64) y; 
      (i64) x - (i64) y <= MAXi32;  @*/
/*@ ensures 
      take PairPost = RW<struct int_pair>(ret);
      PairPost.fst == x + y;
      PairPost.snd == x - y; @*/
{
  ret->fst = x + y;
  ret->snd = x - y;
  return;
}
