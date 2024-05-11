int
main()
/*@ ensures return == 0i32; @*/
{
	if ('a' != 97)
		return 1;
		
	return 0;
}
