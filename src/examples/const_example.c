#define CONST 1
    /*@ function (i32) cn_CONST () { 1i32 } @*/
    // static int c_CONST() /*@ cn_function CONST; @*/ { return CONST; }

int foo (int x)
/*@
  requires true;
  ensures return == cn_CONST();
@*/
{
  return CONST;
}

int main()
/*@ trusted; @*/
{
    int x = 5;
    int res = foo(x);
    /*@ assert(x == 5i32); @*/
    /*@ assert(res == cn_CONST()); @*/
}
