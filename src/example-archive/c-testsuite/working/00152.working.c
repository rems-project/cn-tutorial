#undef  line
#define line 1000

#line line
#if 1000 != __LINE__
	#error "  # line line" not work as expected
#endif

int
main()
/*@ ensures return == 0i32; @*/
{
	return 0;
}
