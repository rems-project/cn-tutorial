/*
error: CreateReadOnly: not a constant ctype: Ivalignof('char[25]')
	p = x(hello)  " is better than bye";
	    ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
*/
// Cause: constant string 

#define x(y) #y

int
main(void)
{
	char *p;
	p = x(hello)  " is better than bye";

	return (*p == 'h') ? 0 : 1;
}
