// Write into a memory cell

void write_1(int *cell)
/*@ requires take CellPre = Owned<int>(cell); @*/
/*@ ensures 
      take CellPost = Owned<int>(cell);
      CellPost == 7i32; @*/
{
  *cell = 7;
}
