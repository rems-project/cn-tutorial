int
main()
/*@ ensures return == 0; @*/
{
	struct T { int x; };
	{
		struct T s;
		s.x = 0;
		return s.x;
	}
}
