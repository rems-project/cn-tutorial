#define BAR 0
#ifdef BAR
	#ifdef FOO
		XXX
		#ifdef FOO
			XXX
		#endif
	#else
		#define FOO
		#ifdef FOO
			int x = BAR;
		#endif
	#endif
#endif

int
main()
/*@ ensures return == 0i32; @*/
{
	return BAR;
}
