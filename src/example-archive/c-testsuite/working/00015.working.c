int
main()
/*@ ensures return == 0; @*/
{
	int arr[2];

	/*@ focus W<int>, 0; @*/
	arr[0] = 1;
	/*@ focus W<int>, 1; @*/
	arr[1] = 2;

	return arr[0] + arr[1] - 3;
}
