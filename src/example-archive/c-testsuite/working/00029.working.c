/*@ lemma one_xor_three() requires true; ensures 1 ^ 3 == 2; @*/
int
main()
/*@ ensures return == 0; @*/
{
	int x;
	
	x = 1;
	x = x ^ 3;
	/*@ apply one_xor_three(); @*/
	return x - 2;
}

