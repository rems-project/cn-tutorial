#define CONST 1
/*@ function (i32) cn_CONST () { 1i32 } @*/

int main()
/*@ trusted; @*/
{
    /*@ assert (cn_CONST() == 1i32); @*/
}
