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
      take L1 = IntList(xs);
      take L2 = IntList(ys);
    ensures
      take L3 = IntList(return);
@*/
{
    if (xs == 0)
    {
        /* unfold append(L1, L2); @*/
        return ys;
    }
    else
    {
        /* unfold append(L1, L2); @*/
        struct int_list *new_tail = int_list_append(xs->tail, ys);
        xs->tail = new_tail;
        return xs;
    }
}

// TODO: How to verify a non-recursive append?
//
// int_list *int_list_append(int_list *l, int_list *r)
// {
//     if (l == NULL)
//     {
//         return r;
//     }
//
//     if (r == NULL)
//     {
//         return l;
//     }
//
//     // Find the last element of l.
//     int_list *p = l;
//     while (p->tail != NULL)
//     /*@
//         inv
//           take r_inv = int_list(r);
//           take l_inv = int_list(l);
//     @*/
//     {
//         p = p->tail;
//     }
//
//     // Add r to l.
//     p->tail = r;
//
//     return l;
// }

void int_list_free(int_list *lst)
/*@
  requires take lst_in = IntList(lst);
  ensures true;
@*/
{
    if (lst == NULL)
    {
        return;
    }

    int_list_free(lst->tail);
    free_int_list_node(lst);
}

int main()
{
    int_list *l = int_list_new(1);
    int_list *r = int_list_new(2);
    int_list *both = int_list_append(l, r);
    int_list_free(both);

    return 0;
}
