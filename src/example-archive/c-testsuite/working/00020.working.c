int
main()
/*@ ensures return == 0i32; @*/
{
	int x, *p, **pp;
	
	x = 0;
	p = &x;
	pp = &p;
	return **pp;
}
