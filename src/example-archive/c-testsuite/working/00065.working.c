#define ADD(X, Y) (X + Y)


int
main()
/*@ ensures return == 0; @*/
{
	return ADD(1, 2) - 3;
}
