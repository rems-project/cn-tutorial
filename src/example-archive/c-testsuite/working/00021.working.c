int
foo(int a, int b)
/*@ requires 
			let mid = (2i64 + (i64) a);
			let res = mid - (i64) b;  
			(i64) MINi32() <= mid; mid <= (i64) MAXi32(); 
			(i64) MINi32() <= res; res <= (i64) MAXi32(); @*/
/*@ ensures return == (2i32 + a) - b; @*/
{
	return 2 + a - b;
}

int
main()
/*@ ensures return == 0i32; @*/
{
	return foo(1, 3);
}

