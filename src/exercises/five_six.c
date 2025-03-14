unsigned int five_six(unsigned int *p, unsigned int *q) 
/*@ requires take P = RW<unsigned int>(p);
		     take Q = RW<unsigned int>(q);
    ensures  take P_post = RW<unsigned int>(p);
    		 take Q_post = RW<unsigned int>(q);
             return == 5;
@*/
{
	*p = 5;
	*q = 6;
	return *p;
}