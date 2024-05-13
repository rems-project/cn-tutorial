#if 1
int x = 0;
#endif

#if 0
int x = 1;
#if 1
 X
#endif
#ifndef AAA
 X
#endif
#endif

int main()
/*@ accesses x; @*/
/*@ requires x == 0i32; @*/
/*@ ensures return == 0i32; @*/
{
	return x;
}
