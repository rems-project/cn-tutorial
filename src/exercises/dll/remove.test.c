#include "./headers.test.h"
#include "./dllist_and_int.test.h"

// Remove the given node from the list and returns another pointer 
// to somewhere in the list, or a null pointer if the list is empty
struct dllist_and_int *remove_current(struct dllist *n)
/* --BEGIN-- */
/*@ requires !is_null(n);
             take Before = Dll_at(n);
             let Del = Node(Before);
    ensures  take Ret = RW<struct dllist_and_int>(return);
             take After = Dll_at(Ret.dllist);
             Ret.data == Del.data;
             (is_null(Del.prev) && is_null(Del.next)) 
               ? After == Empty_Dll{}
               : (!is_null(Del.next) ? 
                    After == Nonempty_Dll {left: Left_Sublist(Before), 
                                           curr: Node(After), 
                                           right: Tl(Right_Sublist(Before))}
                   : After == Nonempty_Dll {left: Tl(Left_Sublist(Before)), 
                                            curr: Node(After), 
                                            right: Right_Sublist(Before)});
@*/
/* --END-- */
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
