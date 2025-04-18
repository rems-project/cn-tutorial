// Write into two memory cells

void write_2(int *cell1, int *cell2)
/*@ requires take Cell1Pre = RW<int>(cell1);
             take Cell2Pre = RW<int>(cell2); @*/
/*@ ensures take Cell1Post = RW<int>(cell1);
            take Cell2Post = RW<int>(cell2);
            Cell1Post == 7i32; Cell2Post == 8i32; @*/
{
  *cell1 = 7;
  *cell2 = 8;
}
