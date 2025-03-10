unsigned int id_by_div_n(unsigned int x, unsigned int n)
/*@ ensures return == x; @*/ 
{
	return (x / n) * n;
}
