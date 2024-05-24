#define NULL ((void*)0)
#define NULL ((void*)0)

#define FOO(X, Y) (X + Y + Z)
#define FOO(X, Y) (X + Y + Z)

#define BAR(X, Y, ...) (X + Y + Z)
#define BAR(X, Y, ...) (X + Y + Z)

int
main()
/*@ ensures return == 0i32; @*/
{
	return 0;
}
