/* 
error: CreateReadOnly: not a constant ctype: Ivalignof('char[6]')
	p = "hello";
	    ^~~~~~~ 
int strlen(char *);
*/
// Cause: constant string 

int
main()
{
	char *p;
	
	p = "hello";
	return strlen(p) - 5;
}
