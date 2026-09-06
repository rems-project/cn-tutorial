int foo(void);
int foo(void);
#define FOO 0

int
main()
/*@ ensures return == 0; @*/
{
	return FOO;
}
