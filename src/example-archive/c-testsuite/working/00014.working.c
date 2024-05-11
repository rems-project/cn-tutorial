int
main()
/*@ ensures return == 0i32; @*/
{
	int x;
	int *p;
	
	x = 1;
	p = &x;
	p[0] = 0;
	return x;
}
