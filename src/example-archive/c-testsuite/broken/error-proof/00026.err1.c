/*
error: CreateReadOnly: not a constant ctype: Ivalignof('char[6]')
	p = "hello";
	    ^~~~~~~ 
*/
// Cause: constant string 

int
main()
{
	char *p;
	
	p = "hello";
	return p[0] - 104;
}
