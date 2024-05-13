int f(int a), g(int a), a;


int
main()
/*@ ensures return == 0i32; @*/
{
	return f(1) - g(1);
}

int
f(int a)
/*@ ensures return == a; @*/
{
	return a;
}

int
g(int a)
/*@ ensures return == a; @*/
{
	return a;
}
