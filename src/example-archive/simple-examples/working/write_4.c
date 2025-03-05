// Write to two static global memory cells

static int *cell1, *cell2;
void write_4()
/*@ accesses cell1, cell2;
    requires
      take Cell1Pre = Owned<int>(cell1);
      take Cell2Pre = Owned<int>(cell2);
    ensures
      take Cell1Post = Owned<int>(cell1);
      take Cell2Post = Owned<int>(cell2);
      Cell1Post == 7i32;
      Cell2Post == 8i32; @*/
{
  *cell1 = 7;
  *cell2 = 8;
}
