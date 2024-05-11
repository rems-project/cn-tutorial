enum E {
	x,
	y,
	z,
};

int
main()
/*@ ensures return == 0i32; @*/
{
	enum E e;

	if(x != 0)
		return 1;
	if(y != 1)
		return 2;
	if(z != 2)
		return 3;
	
	e = x;
	return e;
}

