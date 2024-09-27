#include <stdlib.h>
#include "int_list.h"

int_list *malloc_int_list_node()
/*@ trusted; @*/
{
    return (int_list *)malloc(sizeof(int_list));
}

void free_int_list_node(int_list *p)
/*@ trusted; @*/
{
    free(p);
}

int_list *int_list_new(int head)
{
    int_list *rv = malloc_int_list_node();
    rv->head = head;
    rv->tail = NULL;
    return rv;
}

struct int_list *int_list_append(struct int_list *xs, struct int_list *ys)
/*@
    requires
      // TODO
      true;
    ensures
      // TODO
      true;
@*/
{
    return NULL;
}

void int_list_free(int_list *lst)
/*@
  requires
    // TODO
    true;
  ensures 
    // TODO
    true;
@*/
{
    return;
}

int main()
{
    int_list *l = int_list_new(1);
    int_list *r = int_list_new(2);
    int_list *both = int_list_append(l, r);
    int_list_free(both);

    return 0;
}
