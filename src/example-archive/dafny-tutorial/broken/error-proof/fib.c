// Classic verification problem, the Fibonacci sequence
// TODO: doesn't work as of April 2024 

/*@
function [rec] (integer) fib_spec(integer n)
{
  if (n == 0) { 0 }
  else { if (n == 1) { 1 }
  else { fib_spec(n - 1) + fib_spec(n - 2)}}
}

// Example of lemma syntax:
// https://github.com/rems-project/cerberus/blob/master/tests/cn/mutual_rec/mutual_rec.c

lemma lemma_ord_fib_spec (integer a, integer b)
  requires 0 <= a; a < b;
  ensures fib_spec(a) <= fib_spec(b);
@*/

int compute_fib_2(int n)
/*@ requires 0 <= n; @*/
/*@ requires fib_spec(n) < power(2,31); @*/
// /*@ ensures return == fib_spec(n); @*/
{
  int i = 1;
  int a = 0;
  int b = 1;

  /*@ unfold fib_spec(0); @*/
  if (n == 0)
  {
    return 0;
  };

  /*@ unfold fib_spec(1); @*/
  /*@ apply lemma_ord_fib_spec(1,n); @*/

  while (i < n)
  /*@ inv {n}unchanged; n != 0; @*/
  /*@ inv 0 < i; i <= n; @*/
  /*@ inv a == fib_spec(i - 1); @*/
  /*@ inv b == fib_spec(i); @*/
  /*@ inv 0 <= a; a < b; b <= fib_spec(n); @*/
  /*@ inv i == n ? b == fib_spec(n) : (a + b) < power(2,31); @*/
  {
    /*@ unfold fib_spec(i); @*/
    /*@ unfold fib_spec(i+1); @*/
    int tmp_a = a;
    a = b;
    b = tmp_a + b;
    i = i + 1;
  }

  return b;
}

