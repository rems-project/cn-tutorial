#include "./headers.h"

// Adds after the given node and returns a pointer to the new node
struct node *add(int element, struct node *n)
/*@ requires take Before = Dll_at(n);
    ensures  take After = Dll_at(return);

             is_null(n) ? After == Dll { left: Nil{}, curr: Node(After), right: Nil{}}
                        : After == Dll { left: Cons{Head: Node(Before).data, Tail: Left(Before)}, curr: Node(After), right: Right(Before)};
@*/
{
    struct node *new_node = malloc__node();
    new_node->data = element;
    new_node->prev = 0;
    new_node->next = 0;

    if (n == 0) //empty list case
    {
        new_node->prev = 0;
        new_node->next = 0;
        return new_node;
    } else { 
        /*@ split_case(is_null(n->prev)); @*/
        new_node->next = n->next;
        new_node->prev = n;

        if (n->next !=0) {
            /*@ split_case(is_null(n->next->next)); @*/
            n->next->prev = new_node;
        }

        n->next = new_node;
        return new_node;
    }
}