#define X 1
#undef X

#ifdef X
FAIL
#endif

int
main()
/*@ ensures return == 0; @*/
{
	return 0;
}
