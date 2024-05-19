int
main()
/*@ ensures return == 0i32; @*/
{
	int x;
	int *p;
	
	x = 4;
	p = &x;
	*p = 0;

	return *p;
}
