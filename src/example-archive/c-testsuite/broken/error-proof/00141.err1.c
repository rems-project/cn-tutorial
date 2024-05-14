// Unprovable: this is UB I think

#define CAT(x,y) x ## y
#define XCAT(x,y) CAT(x,y)
#define FOO foo
#define BAR bar

int
main(void)
/*@ ensures return == 0i32; @*/
{
	int foo, bar, foobar;

	CAT(foo,bar) = foo + bar;
	XCAT(FOO,BAR) = foo + bar;
	return 0;
}
