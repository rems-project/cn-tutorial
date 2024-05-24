typedef int myint;
myint x = (myint)1;

int
main(void)
/*@ accesses x; @*/
/*@ requires x == 1i32; @*/
/*@ ensures return == 0i32; @*/
{
	return x-1;
}
