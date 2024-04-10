#include "list.h"
#include "length.c"

struct sized_stack {
  int size;
  struct int_list* data;
};

/*@
datatype sizeAndData {
  SD {unisgned int s, datatype seq d}
}

predicate (datatype seq) SizedStack(pointer p) {
    take S = Owned<struct sized_stack>(p);
    take s = Owned<unsigned int>(S.size);
    take d = IntList(S.data);
    return { s: s, d: d };
  }
}
@*/

