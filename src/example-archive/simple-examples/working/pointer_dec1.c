int a[2];
void b() {
  int *c = &a[1];
  c -= 1;
}

int main(void)
/*@ trusted; @*/
{
  b();
}