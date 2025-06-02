struct S {int a; int b;};
struct S s = { .b = 2, .a = 1};

int
main()
/*@ accesses s;
    requires 
			s.a == 1i32;
			s.b == 2i32;
    ensures return == 0i32; @*/
{
	if(s.a != 1)
		return 1;
	if(s.b != 2)
		return 2;
	return 0;
}
