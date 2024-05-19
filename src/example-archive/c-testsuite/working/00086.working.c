int
main()
/*@ ensures return == 0i32; @*/
{
	short x;
	
	x = 0;
	x = x + 1;
	if (x != 1)
		return 1;
	return 0;
}
