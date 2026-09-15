struct {
  int a;
} b = {{5}};

int main(void)
/*@ trusted; @*/
{
  /*@ assert (b.a == 5); @*/
}