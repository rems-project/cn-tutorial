#include "./headers.test.h"

// Adds after the given node and returns a pointer to the new node
struct dllist *add(int element, struct dllist *n)
/* --BEGIN-- */
/*@ requires take Before = DlList_at(n);
    ensures  take After = DlList_at(return);
             is_null(n) ? 
                After == Nonempty_DlList { 
                           left: Nil{}, 
                           curr: Node(After), 
                           right: Nil{}}
              : After == Nonempty_DlList { 
                           left: Cons {Head: Node(Before).data, 
                                       Tail: Left_Sublist(Before)}, 
                           curr: Node(After), 
                           right: Right_Sublist(Before)};
@*/
/* --END-- */
{
    struct dllist *new_dllist = malloc__dllist();
    new_dllist->data = element;
    new_dllist->prev = 0;
    new_dllist->next = 0;

    if (n == 0) //empty list case
    {
        new_dllist->prev = 0;
        new_dllist->next = 0;
        return new_dllist;
    } else { 
        new_dllist->next = n->next;
        new_dllist->prev = n;

        if (n->next != 0) {
            n->next->prev = new_dllist;
        }

        n->next = new_dllist;
        return new_dllist;
    }
}
