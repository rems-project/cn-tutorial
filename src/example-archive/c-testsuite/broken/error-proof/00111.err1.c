int
main()
/*@ ensures return == 0i32; @*/
{
	short s = 1;
	long l = 1;

	s -= l;
	return s;
}
