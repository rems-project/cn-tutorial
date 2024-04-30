// A finitely bounded loop. Note that CN won't prove this without the invariant,
// although actually we could definitely bounded-model-check it

int loop_4()
/*@ ensures return == 1i32; @*/
{
  int n = 0;
  int acc = 0;

  while (n < 1)
  /*@ inv (n == 0i32 && acc == 0i32)
          ||
          (n == 1i32 && acc == 1i32); @*/
  {
    n++;
    acc++;
  };
  return acc;
}

