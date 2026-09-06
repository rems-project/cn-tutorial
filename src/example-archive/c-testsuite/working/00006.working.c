int
main()
/*@ ensures return == 0; @*/
{
	int x;

	x = 50;
	while (x)
		/*@ inv 0 <= x; x <= 50; @*/
		x = x - 1;
	return x;
}
