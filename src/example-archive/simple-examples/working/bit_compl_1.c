void a() { ~0; }

int main(void)
/*@ trusted; @*/
{
  a();
}
