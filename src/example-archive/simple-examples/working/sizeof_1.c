// Bug: throws a type error
// Derived from src/example-archive/c-testsuite/broken/error-proof/00038.err1.c
// See https://github.com/rems-project/cerberus/issues/272

int
main()
{
	int size1 = sizeof(int);     // <- works 
	size1 = size1 + 1; 					 // <- also works 
	int size2 = sizeof(int) + 1; // <- fails 
}
