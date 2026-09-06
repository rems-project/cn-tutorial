struct S { int a; int b; };
struct S s = {1, 2};

int
main()
/*@ accesses s;
    requires 
			s.a == 1; 
			s.b == 2;
    ensures return == 0; @*/
{
	if(s.a != 1)
		return 1;
	if(s.b != 2)
		return 2;
	return 0;
}
