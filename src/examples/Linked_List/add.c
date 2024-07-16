#include "./headers.h"

// Adds after the given node and returns a pointer to the new node
struct node *add(int element, struct node *n)
/*@ requires take L = Dll_at(n);
             let n_node = Node(L);
             let Left = Left(L);
             let Right = Right(L);
    ensures  take L_ = Dll_at(return);
             let new_node = Node(L_);
             is_null(n) ? L_ == Dll { left: Seq_Nil{}, curr: new_node, right: Seq_Nil{}}
                        : L_ == Dll { left: Seq_Cons{head: n_node.data, tail: Left}, curr: new_node, right: Right};
@*/
{
    struct node *new_node = malloc_node();
    new_node->data = element;
    new_node->prev = 0;
    new_node->next = 0;

    if (n == 0) //empty list case
    {
        new_node->prev = 0;
        new_node->next = 0;
        return new_node;
    } else { 
        /*@ split_case(is_null((*n).next)); @*/
        /*@ split_case(is_null((*n).prev)); @*/

       
        new_node->next = n->next;
        new_node->prev = n;

        if (n->next !=0) {
            /*@ split_case(is_null((*(*n).next).next)); @*/
            n->next->prev = new_node;
        }

        n->next = new_node;
        return new_node;
    }
}