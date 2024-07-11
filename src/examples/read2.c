int read (int *p)
/* --BEGIN-- */
/*@ requires take v1 = Owned<int>(p);
    ensures take v2 = Owned<int>(p);
            return == v1;
            v1 == v2;
@*/
/* --END-- */
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
