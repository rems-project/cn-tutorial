struct { int a; int b; int c; } s = {1, 2, 3};

int
main()
/*@ accesses s;
    requires 
			s.a == 1i32;
			s.b == 2i32; 
			s.c == 3i32;
    ensures return == 0i32; @*/
{
	if (s.a != 1)
		return 1;
	if (s.b != 2)
		return 2;
	if (s.c != 3)
		return 3;

	return 0;
}
