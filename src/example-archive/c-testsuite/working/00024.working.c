typedef struct { int x; int y; } s;

s v;

int
main()
/*@ accesses v; @*/
/*@ ensures return == 0i32; @*/
{
	v.x = 1;
	v.y = 2;
	return 3 - v.x - v.y;
}

