#include "strarray.c"

struct cell {
  char * key;
  unsigned int count;
  struct cell * next;
};

/*@

predicate (datatype cellf) Cells(pointer p) {
    if (is_null(p)) {
        return Cellf_E {};
    }
    else {
        take c = Owned<struct cell>(p);
        take k = Stringa(c.key);
        take n = Cells(c.next);
        return (Cellf_NE { key : k, count : c.count, next : n });
    }
}

@*/

extern struct cell * malloc_cell();
/*@ spec malloc_cell();
    requires 
        true;
    ensures 
      take s = Cells(return);
      s == Cellf_E {};
@*/

extern void free_cell(struct cell * p);
/*@ spec free_cell(pointer p);
    requires 
      take s = Cells(p);
    ensures 
      true;
@*/