int x = 10;

struct S {int a; int *p;};
struct S s = { .p = &x, .a = 1};

int
main()
/*@ accesses s, x;
    requires
			x == 10i32;
			s.p == &x; s.a == 1i32;
    ensures return == 0i32; @*/
{
	if(s.a != 1)
		return 1;
	if(*s.p != 10)
		return 2;
	return 0;
}
