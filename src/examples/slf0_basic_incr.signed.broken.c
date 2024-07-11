void incr (int *p)
/*@ requires take u = Block<int>(p); 
    ensures take v = Owned<int>(p); 
@*/
{
  *p = *p+1;
}

int main()
/*@ trusted; @*/
{
    int x = 5;
    incr(&x);
    /*@ assert (x == 6i32); @*/
}
