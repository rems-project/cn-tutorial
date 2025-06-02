int x, x = 3, x;

int
main()
/*@ accesses x;
    ensures return == 0i32; @*/
{
	if (x != 3)
		return 0;

	x = 0;
	return x;
}

