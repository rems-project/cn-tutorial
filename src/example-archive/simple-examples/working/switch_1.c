void a() {
  switch (0)
    ;
}

int main(void)
/*@ trusted; @*/
{
  a();
}