int doubled (int n) 
--BEGIN--
/*@ requires let n_ = (i64) n;
             -2147483648i64 <= n_ - 1i64; n_ + 1i64 <= 2147483647i64;
             -2147483648i64 <= n_ + n_; n_ + n_ <= 2147483647i64
    ensures return == n * 2i32
@*/
--END--
{
  int a = n+1;
  int b = n-1;
  return a+b;
}
