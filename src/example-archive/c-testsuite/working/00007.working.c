int
main()
/*@ ensures return == 0; @*/
{
	int x;
	
	x = 1;
	for(x = 10; x; x = x - 1)
		/*@ inv 0 <= x; x <= 10; @*/
		;
	if(x)
		return 1;
	x = 10;
	for (;x;)
		/*@ inv 0 <= x; x <= 10; @*/
		x = x - 1;
	return x;
}
