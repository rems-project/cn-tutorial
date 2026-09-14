extern int x; // Testing fails -- linker error because x not defined anywhere

int main()
/*@ ensures return == 0; @*/
{
	return 0;
}
