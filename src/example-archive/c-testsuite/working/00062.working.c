#ifdef FOO
	XXX
#ifdef BAR
	XXX
#endif
	XXX
#endif

#define FOO 1

#ifdef FOO

#ifdef FOO
int x = 0;
#endif

int
main()
/*@ accesses x; @*/
/*@ requires x == 0i32; @*/
/*@ ensures return == 0i32; @*/
{
	return x;
}
#endif



