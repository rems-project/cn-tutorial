// TODO: syntax seems a bit gross here

int a[3] = {0, 1, 2};

int
main()
/*@ accesses a;
    requires 
			a[0] == 0; 
			a[1] == 1; 
			a[2] == 2; 

    ensures return == 0; @*/
{
	/*@ focus RW<int>, 0; @*/
	/*@ focus RW<int>, 1; @*/
	/*@ focus RW<int>, 2; @*/
	if (a[0] != 0)
		return 1;
	if (a[1] != 1)
		return 2;
	if (a[2] != 2)
		return 3;
	
	return 0;
}
