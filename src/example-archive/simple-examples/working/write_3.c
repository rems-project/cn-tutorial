// Write to a memory cell through two aliased pointer variables

void write_3(int *cell1, int *cell2)
/*@ requires 
      take Cell1Pre = RW<int>(cell1);
      cell1 == cell2;
    ensures 
      take Cell2Post = RW<int>(cell2);
      Cell2Post == 8i32; @*/
{
  *cell1 = 7;
  assert(*cell1 == 7 && *cell2 == 7);
  *cell2 = 8;
  assert(*cell1 == 8 && *cell2 == 8);
}
