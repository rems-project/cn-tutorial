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
/*@ requires x == 0i32; @*/
/*@ ensures return == 0i32; @*/
{
	return x;
}
