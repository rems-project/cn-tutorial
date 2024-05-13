#ifndef DEF
int x = 0;
#endif

#define DEF

#ifndef DEF
X
#endif

int
main()
/*@ accesses x; @*/
{
	return x;
}
