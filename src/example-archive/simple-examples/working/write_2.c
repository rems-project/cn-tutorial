// Write into two memory cells

void write_2(int *cell1, int *cell2)
/*@ requires take Cell1Pre = Owned<int>(cell1);
             take Cell2Pre = Owned<int>(cell2); @*/
/*@ ensures take Cell1Post = Owned<int>(cell1);
            take Cell2Post = Owned<int>(cell2);
            Cell1Post == 7i32; Cell2Post == 8i32; @*/
{
  *cell1 = 7;
  *cell2 = 8;
}
