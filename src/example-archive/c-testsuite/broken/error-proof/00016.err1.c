// Should be provable, but doesn't work
// Cause: stack-allocated array 

int
main()
{
	int arr[2];
	int *p;
	
	/*@ extract Block<int>, 1i32; @*/
	p = &arr[1];
	*p = 0;
	return arr[1];
}
