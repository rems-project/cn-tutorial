struct S { int a; int b; };
struct S s = {1, 2};

int
main()
/*@ ensures return == 0i32; @*/
{
	if(s.a != 1)
		return 1;
	if(s.b != 2)
		return 2;
	return 0;
}
