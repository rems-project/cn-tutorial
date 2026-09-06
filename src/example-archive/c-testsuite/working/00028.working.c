/*@ lemma one_and_three() requires true; ensures 1 & 3 == 1; @*/
int
main()
/*@ ensures return == 0; @*/
{
	int x;
	
	x = 1;
	x = x & 3;
	/*@ apply one_and_three(); @*/
	return x - 1;
}

