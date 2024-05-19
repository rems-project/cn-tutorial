// Bug: CN requires extra initialization 
// Derived from src/example-archive/c-testsuite/broken/error-proof/00041.err1.c

// Fails
void loop_4 ()
{
  int i; 
  int t; 

  i = 0; 
  while (i < 1) 
  {
    t = 2; 
    i = 1;
  }
}

// Passes 
void loop_4_unrolled ()
{
  int i; 
  int t; 

  i = 0; 
  // while (i < 1) 
  // {
    t = 2; 
    i = 1;
  // }
}

// Passes
void loop_4_with_redundant_write ()
{
  int i; 
  int t; 

  i = 0; 
  t = 0; // Shouldn't be necessary 
  while (i < 1) 
  {
    t = 2; 
    i = 1;
  }
}

