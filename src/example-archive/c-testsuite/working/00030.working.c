int
f()
/*@ ensures return == 100i32; @*/
{
	return 100;
}

int
main()
/*@ ensures return == 0i32; @*/
{
	if (f() > 1000)
		return 1;
	if (f() >= 1000)
		return 1;
	if (1000 < f())
		return 1;
	if (1000 <= f())
		return 1;
	if (1000 == f())
		return 1;
	if (100 != f())
		return 1;
	return 0;
}

