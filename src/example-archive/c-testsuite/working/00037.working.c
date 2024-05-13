int
main()
/*@ ensures return == 0i32; @*/
{
	int x[2];
	int *p;
	/*@ extract Block<int>, 1u64; @*/
	x[1] = 7;
	p = &x[0];
	p = p + 1;
	
	if(*p != 7)
		return 1;
	if(&x[1] - &x[0] != 1)
		return 1;
	
	return 0;
}
