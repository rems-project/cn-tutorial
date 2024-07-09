#define CONST 1
    /*@ function (i32) CONST () @*/
    static int c_CONST() /*@ cn_function CONST; @*/ { return CONST; }

int foo (int x)
/*@
  requires true;
  ensures return == CONST();
@*/
{
  return CONST;
}
