void incr (int *p)
/* --BEGIN-- */
/*@ requires take v1 = Owned<int>(p);
             ((i64) v1) + 1i64 <= (i64)MAXi32();
    ensures take v2 = Owned<int>(p);
            v2 == v1+1i32;
@*/
/* --END-- */
{
  *p = *p+1;
}
int main()
/*@ trusted; @*/
{
    int x = 0x7fffffff -1;
    incr(&x);
    /*@ assert (x == MAXi32()); @*/
}
