// Write into a memory cell

void write_1(int *cell)
/*@ requires take CellPre = RW<int>(cell);
    ensures 
      take CellPost = RW<int>(cell);
      CellPost == 7i32; @*/
{
  *cell = 7;
}
