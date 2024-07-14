#include "binary_tree.h"

// TODO: Requires queue of pointers
struct int_tree* deepCopyImperative(struct int_tree* p);
/*@ spec deepCopyImperative(pointer p);
    requires
        take T = IntTree(p);
    ensures
        take T_ = IntTree(p);
        T == T_;
        take T2 = IntTree(return);
        T == T2;
@*/
