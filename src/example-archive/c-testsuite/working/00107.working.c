typedef int myint;
myint x = (myint)1;

int
main(void)
/*@ accesses x;
    requires x == 1;
    ensures return == 0; @*/
{
	return x-1;
}
