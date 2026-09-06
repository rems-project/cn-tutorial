struct {
	enum { X } x;
} s;


int
main()
/*@ ensures return == 0; @*/
{
	return X;
}
