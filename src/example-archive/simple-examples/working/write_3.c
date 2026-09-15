// Write to a memory cell through two aliased pointer variables

void write_3(int *cell1, int *cell2)
/*@ requires 
      take Cell1Pre = RW<int>(cell1);
      cell1 == cell2;
    ensures 
      take Cell2Post = RW<int>(cell2);
      Cell2Post == 8; @*/
{
  *cell1 = 7;
  #ifdef CN_INSTRUMENT
  /*@ assert(*cell1 == 7 && *cell2 == 7); @*/
  #else
  assert(*cell1 == 7 && *cell2 == 7);
  #endif
  *cell2 = 8;
  #ifdef CN_INSTRUMENT
  /*@ assert(*cell1 == 8 && *cell2 == 8); @*/
  #else
  assert(*cell1 == 8 && *cell2 == 8);
  #endif
}

int main(void)
/*@ trusted; @*/
{
  int x;
  int *y = &x;
  write_3(&x, y);
}