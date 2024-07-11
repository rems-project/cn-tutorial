int read (int *p, int n, int i)
/*@ requires take a1 = each(i32 j; 0i32 <= j && j < n) { Owned<int>(array_shift<int>(p,j)) };
             0i32 <= i && i < n; 
    ensures take a2 = each(i32 j; 0i32 <= j && j < n) { Owned<int>(array_shift<int>(p,j)) }; @*/
{
  return p[i];
}

int main()
{
    int a[3] = { 0, 1, 2 };

    int zero = read(a, 3, 0);
    /*@ assert (zero == 0i32); @*/
    int *first = a;
    /*@ assert (*first == 0i32); @*/

    int one = read(a, 3, 1);
    /*@ assert (one == 1i32); @*/
    int *second = a + 1;
    /*@ assert (*second == 1i32); @*/

    int two = read(a, 3, 2);
    /*@ assert (two == 2i32); @*/
    int *third = a + 2;
    /*@ assert (*third == 2i32); @*/
}
