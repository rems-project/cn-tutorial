#if 0
X
#elif 0
X
#elif 1
int x = 0;
#endif

int
main()
/*@ accesses x;
    requires x == 0i32;
    ensures return == 0i32; @*/
{
	return x;
}
