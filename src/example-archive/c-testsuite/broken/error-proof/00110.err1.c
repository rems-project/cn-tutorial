extern int x;
int x;

int
main()
/*@ accesses x; @*/
/*@ ensures return == 0i32; @*/
{
	return x;
}
