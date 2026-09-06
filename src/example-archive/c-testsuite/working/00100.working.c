int
foo(void)
/*@ ensures return == 0; @*/
{
	return 0;
}

int
main()
/*@ ensures return == 0; @*/
{
	return foo();
}
