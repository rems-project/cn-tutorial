int
foo(void)
/*@ ensures return == 0i32; @*/
{
	return 0;
}

int
main()
/*@ ensures return == 0i32; @*/
{
	return foo();
}
