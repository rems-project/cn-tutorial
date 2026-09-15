// Write into a memory cell

void write_1(int *cell)
/*@ requires take CellPre = RW<int>(cell);
    ensures 
      take CellPost = RW<int>(cell);
      CellPost == 7; @*/
{
  *cell = 7;
}

int main(void)
/*@ trusted; @*/
{
  int x = 10;
  write_1(&x);
}