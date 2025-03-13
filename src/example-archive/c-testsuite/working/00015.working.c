int
main()
/*@ ensures return == 0i32; @*/
{
	int arr[2];

	/*@ focus W<int>, 0u64; @*/
	arr[0] = 1;
	/*@ focus W<int>, 1u64; @*/
	arr[1] = 2;

	return arr[0] + arr[1] - 3;
}
