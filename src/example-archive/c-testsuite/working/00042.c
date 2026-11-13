[[cerb::byte]] typedef unsigned char byte;

int
main()
{
	union { int a; int b; } u;
	/*@ from_bytes W<int>(&u); @*/
	u.a = 1;
	u.b = 3;
	
	if (u.a != 3 || u.b != 3) {
		return 1;
	}
	/*@ to_bytes RW<int>(&u); @*/
	return 0;
}
