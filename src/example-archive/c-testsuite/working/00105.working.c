int
main()
/*@ ensures return == 0i32; @*/
{
	int i;

	for(i = 0; i < 10; i++)
		if (!i)
			continue;
	
	return 0;
}
