int
main()
/*@ ensures return == 0i32; @*/
{
	struct T { int x; };
	{
		struct T s;
		s.x = 0;
		return s.x;
	}
}
