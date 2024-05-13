// Currently unprovable: do-while not supported 

int
main()
/*@ ensures return == 0i32; @*/
{
	int x;

	x = 50;
	do 
		x = x - 1;
	while(x);
	return x;
}
