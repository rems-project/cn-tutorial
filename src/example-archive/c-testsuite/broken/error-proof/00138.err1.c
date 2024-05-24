/*
error: CreateReadOnly: not a constant ctype: Ivalignof('char[3]')
	char *a = A(M,"hi");
	          ^~~~ 
*/
// Cause: constant string 

#define M(x) x
#define A(a,b) a(b)

int
main(void)
{
	char *a = A(M,"hi");

	return (a[1] == 'i') ? 0 : 1;
}
