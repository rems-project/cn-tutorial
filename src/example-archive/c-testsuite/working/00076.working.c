int
main()
/*@ ensures return == 0i32; @*/
{
	if(0 ? 1 : 0)
		return 1;
	if(1 ? 0 : 1)
		return 2;
	return 0;
}
