#include "./headers.h"

// removes the given node from the list and returns another pointer 
// to somewhere in the list, or a null pointer if the list is empty.
struct node_and_int *remove(struct node *n)
/*@ requires !is_null(n);
             take before = Dll_at(n);
             let del = Node(before);
    ensures  take ret = Owned<struct node_and_int>(return);
             take after = Dll_at(ret.node);
             (is_null(del.prev) && is_null(del.next)) ? after == Empty_Dll{}
                 : (!is_null(del.next) ? after == Dll{left: Left(before), n: Node(after), right: tl(Right(before))}
                     : after == Dll{left: tl(Left(before)), n: Node(after), right: Right(before)});
@*/
{
    if (n == 0) { //empty list case
        struct node_and_int *pair = malloc_node_and_int();
        pair->node = 0;  //null pointer
        pair->data = 0;
        return pair;
    } else { 
        struct node *temp = 0;
        if (n->prev != 0) {
            /*@ split_case(is_null((*(*n).prev).prev)); @*/

            n->prev->next = n->next;
            temp = n->prev;
        }
        if (n->next != 0) {
            /*@ split_case(is_null((*(*n).next).next)); @*/
            n->next->prev = n->prev;
            temp = n->next;
        }

        struct node_and_int *pair = malloc_node_and_int();
        pair->node = temp;
        pair->data = n->data;

        free_node(n);       
        return pair;
    }
}