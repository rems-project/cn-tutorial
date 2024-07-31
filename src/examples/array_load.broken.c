int read (int *p, int n, int i)
/*@ requires take A = each(i32 j; 0i32 <= j && j < n) { 
                        Owned<int>(array_shift<int>(p,j)) };
             0i32 <= i && i < n; 
    ensures take A_post = each(i32 j; 0i32 <= j && j < n) { 
                        Owned<int>(array_shift<int>(p,j)) }; 
@*/
{
  return p[i];
}
