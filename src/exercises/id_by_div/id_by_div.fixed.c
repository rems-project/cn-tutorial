unsigned int id_by_div(unsigned int x)
/*@ requires x % 2u32 == 0u32;
	ensures return == x; @*/ 
{
	return (x / 2) * 2;
}