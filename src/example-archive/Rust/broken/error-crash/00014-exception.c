// Tags: arrays

// Tags: main, pointers
/** Description: 

Exception triggered by a spec creating arrays.
    
*/


// Allocates and populates an array of size `len`. 
extern int *createArray (unsigned int len);
/*@ spec createArray(pointer p, u32 len);
    requires true;
    ensures  take vp1 = each(u32 i; i < len) { Owned<int>( array_shift<int>(return, i)) };
@*/
