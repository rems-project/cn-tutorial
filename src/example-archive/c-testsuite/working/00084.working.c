#define ARGS(...) __VA_ARGS__

int
none()
/*@ ensures return == 0; @*/
{
	return 0;
}

int
one(int a)
/*@ ensures 
			return == (a != 1 ? 1 : 0); @*/
{
	if (a != 1)
		return 1;
	
	return 0;
}

int
two(int a, int b)
/*@ ensures 
			return == (a != 1 ? 1 : 
									(b != 2 ? 1 : 0 )); @*/
{
	if (a != 1)
		return 1;
	if (b != 2)
		return 1;
	
	return 0;
}

int
three(int a, int b, int c)
/*@ ensures 
			return == (a != 1 ? 1 : 
									(b != 2 ? 1 : 
										(c != 3 ? 1 : 0 ))); @*/
{
	if (a != 1)
		return 1;
	if (b != 2)
		return 1;
	if (c != 3)
		return 1;
	
	return 0;
}

int
main()
/*@ ensures return == 0; @*/
{
	if (none(ARGS()))
		return 1;
	if (one(ARGS(1)))
		return 2;
	if (two(ARGS(1, 2)))
		return 3;
	if (three(ARGS(1, 2, 3)))
		return 4;
	return 0;
}
