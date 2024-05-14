// Crash: caused by pointer decrement 

int
main()
/*@ ensures return == 0i32; @*/
{
	int arr[2];
	int *p;

	/*@ extract Block<int>, 0u64; @*/
	arr[0] = 2;
	/*@ extract Block<int>, 1u64; @*/
	arr[1] = 3;
	p = &arr[0];
	if(*(p++) != 2)
		return 1;
	if(*(p++) != 3)
		return 2;
	
	p = &arr[1];
	if(*(p--) != 3)
		return 1;
	if(*(p--) != 2)
		return 2;
		
	p = &arr[0];
	if(*(++p) != 3)
		return 1;
	
	p = &arr[1];
	if(*(--p) != 2) // <-- cause of the crash  
		return 1;

	return 0;
}
