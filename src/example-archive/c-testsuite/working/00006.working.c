int
main()
/*@ ensures return == 0i32; @*/
{
	int x;

	x = 50;
	while (x)
		/*@ inv 0i32 <= x; x <= 50i32; @*/
		x = x - 1;
	return x;
}
