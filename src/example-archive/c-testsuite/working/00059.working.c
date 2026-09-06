int
main()
/*@ ensures return == 0; @*/
{
	if ('a' != 97)
		return 1;
		
	return 0;
}
