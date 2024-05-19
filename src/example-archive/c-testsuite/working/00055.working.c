enum E {
	x,
	y = 2,
	z,
};

int
main()
/*@ ensures return == 0i32; @*/
{
	enum E e;

	if(x != 0)
		return 1;
	if(y != 2)
		return 2;
	if(z != 3)
		return 3;
	
	e = x;
	return e;
}

