#define CALL(FUN, ...) FUN(__VA_ARGS__)

int
one(int a)
/*@ ensures 
			return == (a != 1i32 ? 1i32 : 0i32); @*/
{
	if (a != 1)
		return 1;
	
	return 0;
}

int
two(int a, int b)
/*@ ensures 
			return == (a != 1i32 ? 1i32 : 
									(b != 2i32 ? 1i32 : 0i32 )); @*/
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
			return == (a != 1i32 ? 1i32 : 
									(b != 2i32 ? 1i32 : 
										(c != 3i32 ? 1i32 : 0i32 ))); @*/
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
/*@ ensures return == 0i32; @*/
{
	if (CALL(one, 1))
		return 2;
	if (CALL(two, 1, 2))
		return 3;
	if (CALL(three, 1, 2, 3))
		return 4;
	
	return 0;
}
