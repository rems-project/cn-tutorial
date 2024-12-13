// This file show how we envision using the preprocessor.


#define S 11111111

int some_other_fun(int x)
/*@ requires true; ensures return == 0i32; @*/
{
  return 0;
}

int inc(int x)
/*@ requires 0i32 <= x && x < 10i32; ensures  return < 11i32; @*/
{
#if !CN_MUTATE_inc
  return x + 1;
#elif X_PLUS_2
  return x + 2;
#elif X_PLUS_3
  return x + 3;
#endif
}


#if CN_TEST_A // fails
int A() {
  inc(S);
}
#endif

#if CN_TEST_B
int B() {
  inc(5);
}
#endif




