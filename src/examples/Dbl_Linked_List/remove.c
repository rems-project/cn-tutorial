#include "./headers.h"

// removes the given node from the list and returns another pointer 
// to somewhere in the list, or a null pointer if the list is empty.
struct node_and_int *remove(struct node *n)
/*@ requires !is_null(n);
             take Before = Dll_at(n);
             let del = Node(Before);
    ensures  take ret = Owned<struct node_and_int>(return);
             take After = Dll_at(ret.node);
             (is_null(del.prev) && is_null(del.next)) ? After == Empty_Dll{}
                 : (!is_null(del.next) ? After == Dll{left: Left(Before), curr: Node(After), right: tl(Right(Before))}
                     : After == Dll{left: tl(Left(Before)), curr: Node(After), right: Right(Before)});
@*/
{
    if (n == 0) { //empty list case
        struct node_and_int *pair = malloc_node_and_int();
        pair->node = 0; 
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