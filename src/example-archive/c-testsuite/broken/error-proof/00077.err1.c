// In progress... 

int
foo(int x[100])
/*@ requires 
			take PreX = each (u64 j; 0u64 <= j && j < 100u64) {Owned<int>(x + j)}; @*/
{
	int y[100];
	int *p;
	
	/*@ extract Block<int>, 0u64; @*/
	y[0] = 2000;
	
	if(x[0] != 1000)
	{
		return 1;
	}
	
	p = x;
	
	if(p[0] != 1000)
	{
		return 2;
	}
	
	p = y;
	
	if(p[0] != 2000)
	{
		return 3;
	}
	
	if(sizeof(x) != sizeof(void*))
	{
		return 4;
	}
	
	if(sizeof(y) <= sizeof(x))
	{
		return 5;
	}
	
	return 0;
}

int
main()
/*@ ensures return == 0i32; @*/
{
	int x[100];
	assert(0); 
	/*@ extract Block<int>, 0u64; @*/
	x[0] = 1000;
	
	return foo(x);
}
