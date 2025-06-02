// Assign to a memory cell, then dispose it using free() 

// free() is not defined by default in CN. We can define a fake version that
// only works on ints.

void my_free_int(int *target)
/*@ trusted;
    requires take ToFree = RW<int>(target); @*/
{}

void free_1(int *x, int *y)
/*@ requires 
      take Xpre = RW<int>(x); 
      take Ypre = RW<int>(y);
    ensures take Ypost = RW<int>(y); @*/
{
  *x = 7;
  my_free_int(x);
  // *x = 7; // <-- Would generate an error
}
