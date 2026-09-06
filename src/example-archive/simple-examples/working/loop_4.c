// A finitely bounded loop. Note that CN won't prove this without the invariant,
// although actually we could definitely bounded-model-check it

int loop_4()
/*@ ensures return == 1; @*/
{
  int n = 0;
  int acc = 0;

  while (n < 1)
  /*@ inv (n == 0 && acc == 0)
          ||
          (n == 1 && acc == 1); @*/
  {
    n++;
    acc++;
  };
  return acc;
}

