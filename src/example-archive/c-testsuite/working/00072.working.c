int
main()
/*@ ensures return == 0i32; @*/
{
	int arr[2];
	int *p;
	/*@ focus W<int>, 1u64; @*/
	p = &arr[0];
	p += 1;
	*p = 123;
	
	if(arr[1] != 123)
		return 1;
	return 0;
}
