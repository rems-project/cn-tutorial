// Assign to a memory cell, then dispose it using free() 

// free() is not defined by default in CN. We can define a fake version that
// only works on ints.

#ifdef CN_INSTRUMENT
void cn_free_sized(void*, unsigned long len);
#endif

void my_free_int(int *target)
/*@ trusted;
    requires take ToFree = RW<int>(target); @*/
{
  #ifdef CN_INSTRUMENT
  cn_free_sized(target, sizeof(int));
  #endif
}

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


int main(void)
/*@ trusted; @*/
{
  #ifdef CN_INSTRUMENT
  int x = 5, y = 42;
  free_1(&x, &y);
  #endif
}
