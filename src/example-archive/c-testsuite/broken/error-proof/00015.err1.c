int
main()
{
	int arr[2];

	/*@ extract Block<int>, 0; @*/
	arr[0] = 1;
	arr[1] = 2;

	return arr[0] + arr[1] - 3;
}
