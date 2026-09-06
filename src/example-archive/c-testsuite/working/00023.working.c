int x;

int
main()
/*@ accesses x;
    ensures return == 0; @*/
{
	x = 0;
	return x;
}

