/*@ lemma one_or_four() requires true; ensures 1 | 4 == 5; @*/
int
main()
/*@ ensures return == 0; @*/
{
	int x;
	
	x = 1;
	x = x | 4;
	/*@ apply one_or_four(); @*/
	return x - 5;
}

