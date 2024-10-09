int doubled (int n)
/* --BEGIN-- */
/*@ requires let N = (i64) n;
             (i64)MINi32() <= N - 1i64; N + 1i64 <= (i64)MAXi32();
             (i64)MINi32() <= N + N; N + N <= (i64)MAXi32();
    ensures return == n * 2i32;
@*/
/* --END-- */
{
  int a = n+1;
  int b = n-1;
  return a+b;
}
