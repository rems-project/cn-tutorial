int
main()
/*@ ensures return == 0; @*/
{
	int x;
	
	x = 1;
	if ((x << 1) != 2)
		return 1;
	
	return 0;
}
