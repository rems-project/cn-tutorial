int a[] = {1, 2, 3, 4};

int
main()
/*@ ensures return == 0i32; @*/
{
	if (sizeof(a) != 4*sizeof(int))
		return 1;
	
	return 0;
}
