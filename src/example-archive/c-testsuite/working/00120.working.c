struct {
	enum { X } x;
} s;


int
main()
/*@ ensures return == 0i32; @*/
{
	return X;
}
