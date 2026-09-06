#if 0
X
#elif 1
int x = 0;
#else
X
#endif

int
main()
/*@ accesses x;
    requires x == 0;
    ensures return == 0; @*/
{
	return x;
}
