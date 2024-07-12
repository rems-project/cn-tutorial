// #include <limits.h>
// Generating C files from CN-annotated source... cn: internal error, uncaught exception:
//     End_of_file

int quadruple_mem (int *p)
/* --BEGIN-- */
/*@ requires take n = Owned<int>(p);
             let n_ = (i64) n;
             (i64)MINi32() <= n_ * 4i64; n_ * 4i64 <= (i64)MAXi32();
    ensures take n2 = Owned<int>(p);
            n2 == n;
            return == 4i32 * n;
 @*/
/* --END-- */
{
  int m = *p + *p;
  return m + m;
}

int main()
/*@ trusted; @*/
{

    int x = 20;
    int res = quadruple_mem(&x);
    /*@ assert (x == 20i32); @*/
    /*@ assert (res == 80i32); @*/
}
