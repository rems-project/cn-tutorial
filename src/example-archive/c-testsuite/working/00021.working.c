int
foo(int a, int b)
/*@ requires 
			let mid = (2 + a);
			let res = mid - b;  
			MINi32() <= mid; mid <= MAXi32(); 
			MINi32() <= res; res <= MAXi32(); 
    ensures return == (2 + a) - b; @*/
{
	return 2 + a - b;
}

int
main()
/*@ ensures return == 0; @*/
{
	return foo(1, 3);
}

