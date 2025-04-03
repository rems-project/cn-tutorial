#include "./headers.verif.h"
#include "./dllist_and_int.verif.h"

// Remove the given node from the list and returns another pointer 
// to somewhere in the list, or a null pointer if the list is empty
struct dllist_and_int *remove(struct dllist *n)
/*@ requires !is_null(n);
             take Before = DlList_at(n);
             let Del = Node(Before);
    ensures  take Ret = RW<struct dllist_and_int>(return);
             take After = DlList_at(Ret.dllist);
             Ret.data == Del.data;
             (is_null(Del.prev) && is_null(Del.next)) 
               ? After == Empty_DlList{}
               : (!is_null(Del.next) ? 
                    After == Nonempty_DlList {left: Left_Sublist(Before), 
                                           curr: Node(After), 
                                           right: Tl(Right_Sublist(Before))}
                   : After == Nonempty_DlList {left: Tl(Left_Sublist(Before)), 
                                            curr: Node(After), 
                                            right: Right_Sublist(Before)});
@*/
{
    struct dllist *temp = 0;
    if (n->prev != 0) {
/* --BEGIN-- */
        /*@ split_case(is_null(n->prev->prev)); @*/
/* --END-- */
        n->prev->next = n->next;
        temp = n->prev;
    }
    if (n->next != 0) {
/* --BEGIN-- */
        /*@ split_case(is_null(n->next->next)); @*/
/* --END-- */
        n->next->prev = n->prev;
        temp = n->next;
    }

    struct dllist_and_int *pair = malloc__dllist_and_int();
    pair->dllist = temp;
    pair->data = n->data;

    free__dllist(n);       
    return pair;
}
