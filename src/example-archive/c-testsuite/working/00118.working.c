int
main()
/*@ ensures return == 0; @*/
{
	struct { int x; } s = { 0 };
	return s.x;
}
