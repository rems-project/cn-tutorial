int
f1(char *p)
/*@ requires 
			take PreP = RW<char>(p);
    ensures 
			take PostP = RW<char>(p);
			return == 1i32 + (i32) PreP; @*/
{
	return *p+1;
}

int
main()
/*@ ensures return == 0i32; @*/
{
	char s = 1;
	int v[1000];
	int f1(char *);

	if (f1(&s) != 2)
		return 1;
	return 0;
}
