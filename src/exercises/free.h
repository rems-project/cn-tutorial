extern void free__int (int *p);
/*@ spec free__int(pointer p);
    requires take P = W<int>(p);
    ensures true;
@*/


extern void free__unsigned_int (unsigned int *p);
/*@ spec free__unsigned_int(pointer p);
    requires take P = W<unsigned int>(p);
    ensures true;
@*/

