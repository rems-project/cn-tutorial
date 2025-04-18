#include "malloc.h"

void do_nothing (unsigned int* p)
/*@ 
requires take P = RW<unsigned int>(p);
ensures take P_post = RW<unsigned int>(p);
@*/
{
}

unsigned int* create (unsigned int x)
/*@ 
ensures take P = RW<unsigned int>(return);
		P == x;
@*/
{
	unsigned int* p = malloc__unsigned_int();
	do_nothing(p);
	*p = x;
	return p;
}