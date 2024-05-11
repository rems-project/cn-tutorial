int x = 5;
long y = 6;
int *p = &x;

int
main()
/*@ accesses x; y; p;  @*/
/*@ requires 
			take PreP = Owned<int>(p); @*/
/*@ ensures 
			take PostP = Owned<int>(p); 
			return != 5i32; @*/
{
	if (x != 5) 
		return 1;
	if (y != 6)
		return 2;
	if (*p != 5)
		return 3;
	return 0;
}

