#define x f
#define y() f

typedef struct { int f; } S;

int
main()
/*@ ensures return == 0i32; @*/
{
	S s;

	s.x = 0;
	return s.y();
}
