int x = 5;
long y = 6;
int *p = &x;

int
main()
/*@ accesses x, y, p;
    requires
			x == 5i32;
			y == 6i64;
			p == &x;
    ensures return == 0i32; @*/
{
	if (x != 5)
		return 1;
	if (y != 6)
		return 2;
	if (*p != 5)
		return 3;
	return 0;
}

