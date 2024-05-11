int
f(int f)
/*@ ensures return == f; @*/
{
	return f;
}

int
main()
/*@ ensures return == 0i32; @*/
{
	return f(0);
}
