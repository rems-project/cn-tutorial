int
main()
/*@ ensures return == 0i32; @*/
{
	void *p;
	int x;
	
	x = 2;
	p = &x;
	
	if(*((int*)p) != 2)
		return 1;
	return 0;
}
