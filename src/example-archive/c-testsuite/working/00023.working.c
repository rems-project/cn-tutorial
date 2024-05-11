int x;

int
main()
/*@ accesses x; @*/
/*@ ensures return == 0i32; @*/
{
	x = 0;
	return x;
}

