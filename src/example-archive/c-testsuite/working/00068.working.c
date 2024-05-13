#if 0
X
#elif 1
int x = 0;
#else
X
#endif

int
main()
/*@ accesses x; @*/
{
	return x;
}
