int read (int *p)
/*@ requires take v1 = Owned<int>(p); @*/
{
  return *p;
}

int main()
/*@ trusted; @*/
{
    int x = 5;
    int res = read(&x);
    /*@ assert (res == 5i32); @*/
    /*@ assert (x == 5i32) ;@*/
}
