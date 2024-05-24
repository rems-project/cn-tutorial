int
main()
/*@ ensures return == 0i32; @*/
{
	unsigned long long x;
	
	x = 0;
	x = x + 1;
	if (x != 1)
		return 1;
	return 0;
}
