int
main()
/*@ ensures return == 0i32; @*/
{
	int x;
	
	x = 1;
	x = x | 4;
	return x - 5;
}

