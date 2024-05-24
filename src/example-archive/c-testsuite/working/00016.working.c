int
main()
/*@ ensures return == 0i32; @*/
{
	int arr[2];
	int *p;
	
	/*@ extract Block<int>, 1u64; @*/
	p = &arr[1];
	*p = 0;
	return arr[1];
}
