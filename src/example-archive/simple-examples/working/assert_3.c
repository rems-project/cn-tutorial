// Assert and prove a property about memory cells. Uses the lemma-hack way of
// asserting memory properties 

// Define a lemma that asserts ownership of a particular memory cell 
/*@
  lemma assert_own (pointer p)
  requires take x0 = RW<int>(p);
  ensures  
    take x1 = RW<int>(p);
    x1 == x0; // <-- Note, otherwise the lemma havocs the memory contents 
@*/

void assert_3(int *x, int *y)
/*@ requires 
      take Xpre = RW<int>(x); 
      take Ypre = RW<int>(y);
      *x == 7i32; *y == 7i32;
    ensures 
      take Xpost = RW<int>(x);
      take Ypost = RW<int>(y);
      *x == 0i32; *y == 0i32; @*/
{
  *x = 0;
  assert(*x == 0 && *y == 7);

  // Apply the lemma to x / y 
  /*@ apply assert_own(x); @*/
  /*@ apply assert_own(y); @*/

  assert(*x == 0 && *y == 7);
  *y = 0;
  assert(*x == 0 && *y == 0);
}

