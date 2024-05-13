// Currently unprovable: goto unsupported 

int
main()
/*@ ensures return == 0i32; @*/
{
	start:
		goto next;
		return 1;
	success:
		return 0;
	next:
	foo:
		goto success;
		return 1;
}
