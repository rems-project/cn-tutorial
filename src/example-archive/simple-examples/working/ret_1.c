// Return zero. This can't fault, and therefore requires no CN annotations.

int ret_1()
{
  return 0;
}

int main(void)
/*@ trusted; @*/
{
  ret_1();
}