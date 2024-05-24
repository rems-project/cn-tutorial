int
main()
/*@ ensures return == 0i32; @*/
{
	struct { int x; } s = { 0 };
	return s.x;
}
