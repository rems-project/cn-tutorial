// This file show how we envision using the preprocessor.
#define S 11111111

int puts(const char*);

int some_other_fun(int x)
/*@ requires true; ensures return == 1i32; @*/
{
  return 0;
}

int inc(int x)
/*@ requires 0i32 <= x && x < 10i32; ensures  return < 11i32; @*/
{
#if !MUTATION(inc)
  return x + 1;
#elif X_PLUS_2
  return x + 2;
#elif X_PLUS_3
  return x + 3;
#endif
}


#if CN_TEST_A
int main(int argc, char* argv[]) {
  return inc(S);
}
#endif

#if CN_TEST_B
int main(int argc, char* argv[]) {
  return inc(5);
}
#endif




