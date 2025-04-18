// Should be provable but doesn't work
// Cause: lack of frame preservation for global variables 
// Derived from src/example-archive/c-testsuite/broken/error-proof/00033.err1.c

int g;

void
write_g_to_1()
/*@ requires 
        take Pre = W<int>(&g); @*/
/*@ ensures 
        take Post = RW<int>(&g); 
        Post == 1i32; @*/
{
	g = 1;
}


int
effect_1()
/*@ requires 
      take Pre = W<int>(&g); @*/
/*@ ensures 
      take Post = RW<int>(&g); 
      return == 1i32; @*/
{
  int x;
  
  g = 0;
  write_g_to_1(); 
  if(g)
    return 1;
  return 0; 
} 