int
main()
/*@ ensures return == 0; @*/
{
	int arr[2];
	int *p;
	
	/*@ focus W<int>, 1; @*/
	p = &arr[1];
	*p = 0;
	return arr[1];
}
