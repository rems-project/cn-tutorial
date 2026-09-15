int neg_1(int i) 
/*@ requires i > MINi32(); @*/
{
  return -i; 
}

int main(void)
/*@ trusted; @*/
{
  int r = neg_1(42);
  /*@ assert (r == -42); @*/
}