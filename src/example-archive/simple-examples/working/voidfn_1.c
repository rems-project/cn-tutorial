void a() { return; }

int main(void)
/*@ trusted; @*/
{
  a();
}