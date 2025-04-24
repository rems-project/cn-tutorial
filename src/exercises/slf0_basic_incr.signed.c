void incr (int *p)
/*@ requires take P = RW<int>(p);
             ((i64) P) + 1i64 <= (i64) MAXi32();
    ensures take P_post = RW<int>(p);
            P_post == P + 1i32;
@*/
{
  *p = *p+1;
}
