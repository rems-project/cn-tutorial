#include "cell.c"

enum {N = 109};

struct hashtable {
  struct cell *buckets[N];
};

/*@
predicate (datatype hashtablef) Hashtable(pointer p) {
    take h = Owned<struct hashtable>(p);
    let pb = member_shift<hashtable>(p, buckets); 
    //TODO: member_shift would be helpful in the tutorial
    take bs = each(u64 j; j < (u64) N()) { Cells(array_shift<struct cell *>(pb, j)) };
    return to_hashtablef(bs);
}

function (datatype hashtablef) to_hashtablef(map<u64, datatype cellf> bs) {
  to_hashtablef_aux(bs, 0u64)
}

function [rec] (datatype hashtablef) to_hashtablef_aux(map<u64, datatype cellf> buckets, u64 offset) {
   if (N() - offset <= 0u64) {
    Hashtablef_E {}
   }
   else {
    let bt = buckets[offset];
    Hashtablef_NE { head : bt, tail : to_hashtablef_aux(buckets, offset + 1u64)}
   }
}
@*/

extern struct hashtable * malloc_hashtable();
/*@ spec malloc_hashtable();
    requires 
        true;
    ensures 
      take h = Hashtable(return);
@*/

extern void free_hashtable(char * p);
/*@ spec free_hashtable(pointer p);
    requires 
      take h = Hashtable(p);
    ensures 
      true;
@*/