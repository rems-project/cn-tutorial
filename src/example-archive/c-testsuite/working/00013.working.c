int
main()
/*@ ensures return == 0i32; @*/
{
	int x;
	int *p;
	
	x = 0;
	p = &x;
	return p[0];
}
