unsigned int id_by_div(unsigned int x)
/*@ ensures return == x; @*/ 
{
	return (x / 2) * 2;
}