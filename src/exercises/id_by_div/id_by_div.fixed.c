unsigned int id_by_div(unsigned int x)
/*@ requires rem(x, 2) == 0;
	ensures return == x; @*/ 
{
	return (x / 2) * 2;
}
