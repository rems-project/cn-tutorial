int x = 10;

struct S {int a; int *p;};
struct S s = { .p = &x, .a = 1};

int
main()
/*@ accesses s, x;
    requires
			x == 10;
			s.p == &x; s.a == 1;
    ensures return == 0; @*/
{
	if(s.a != 1)
		return 1;
	if(*s.p != 10)
		return 2;
	return 0;
}
