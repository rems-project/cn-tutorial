int
main()
/*@ ensures return == 0i32; @*/
{
	int x;
	
	x = 1;
	x = x & 3;
	return x - 1;
}

