#define x(y) ((y) + 1)

int
main()
/*@ ensures return == 0i32; @*/
{
	int x;
	int y;
	
	y = 0;
	x = x(y);
	
	if(x != 1)
		return 1;
	
	return 0;
}

