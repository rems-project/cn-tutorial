// TODO: syntax seems a bit gross here

int a[3] = {0, 1, 2};

int
main()
/*@ accesses a;
    requires 
			a[0u64] == 0i32; 
			a[1u64] == 1i32; 
			a[2u64] == 2i32; 

    ensures return == 0i32; @*/
{
	/*@ focus RW<int>, 0u64; @*/
	/*@ focus RW<int>, 1u64; @*/
	/*@ focus RW<int>, 2u64; @*/
	if (a[0] != 0)
		return 1;
	if (a[1] != 1)
		return 2;
	if (a[2] != 2)
		return 3;
	
	return 0;
}
