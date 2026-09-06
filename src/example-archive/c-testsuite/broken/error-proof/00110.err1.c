extern int x;
int x;

int
main()
/*@ accesses x; @*/
/*@ ensures return == 0; @*/
{
	return x;
}
