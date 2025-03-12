#include "./headers.verif.h"
#include "./dllist_and_int.h"

// removes the given node from the list and returns another pointer 
// to somewhere in the list, or a null pointer if the list is empty.
struct dllist_and_int *remove(struct dllist *n)
{
    struct dllist *temp = 0;
    if (n->prev != 0) {
        n->prev->next = n->next;
        temp = n->prev;
    }
    if (n->next != 0) {
        n->next->prev = n->prev;
        temp = n->next;
    }

    struct dllist_and_int *pair = malloc__dllist_and_int();
    pair->dllist = temp;
    pair->data = n->data;

    free__dllist(n);       
    return pair;
}