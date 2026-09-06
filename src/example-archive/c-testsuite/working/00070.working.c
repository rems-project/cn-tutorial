#ifndef DEF
int x = 0;
#endif

#define DEF

#ifndef DEF
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
