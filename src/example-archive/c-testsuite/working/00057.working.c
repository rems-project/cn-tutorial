int
main()
/*@ ensures return == 0; @*/
{
	char a[16], b[16];
	
	if(sizeof(a) != sizeof(b))
		return 1;
	return 0;
}
