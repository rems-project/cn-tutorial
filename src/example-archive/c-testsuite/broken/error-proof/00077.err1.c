// In progress... 

int
foo(int x[100])
/*@ requires 
			take PreX = each (integer j; 0 <= j && j < 100) {RW<int>(x + j)}; 
	ensures 
			take PostX = each (integer j; 0 <= j && j < 100) {RW<int>(x + j)}; 
@*/
{
	int y[100];
	int *p;
	
	/*@ focus W<int>, 0u64; @*/
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
/*@ ensures return == 0; @*/
{
	int x[100];
	#ifndef CN_INSTRUMENT
	assert(0); 
	#endif
	/*@ focus W<int>, 0; @*/
	x[0] = 1000;
	
	return foo(x);
}
