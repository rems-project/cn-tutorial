#include "./headers.h"

/* TODO: I want the spec to say that the first half and the second half of the list 
 * (First and Rest) are the same, there is just an extra node in the middle.
 * Currently the spec is saying the following:

 * When we first call LinkedList(n), we get the first part, the node n points to, 
 * and the rest of the list. When we add a new node and call LinkedList on the new node,
 * the old node is squished into the first part. Then we have the new node and then the 
 * rest of the list stays the same. The first paragraph of specs is making sure all of the 
 * pointers are correct. The second paragraph is making sure that the two halves of the list
 * are the same, except for the new node added to the beginning of First.

 * We have to include in these specs whether or not the given node was null.
 
 * I believe the spec currently is correct, but it is very verbose and hard to understand.
 * I would like to find a simpler version. Maybe even write a correctness function?
*/




// Adds after the given node
struct node *add(int element, struct node *n)
/*@ requires take L = LinkedList(n);
             let node = Dll_Node(L);
             let First = Dll_First(L);
             let Rest = Dll_Rest(L);
    ensures  take L_ = LinkedList(return);
             let First_ = Dll_First(L_);
             let Rest_ = Dll_Rest(L_);
             let new_node = Dll_Node(L_);

             ptr_eq(new_node.prev, n);
             let node_ = Seq_Node_Head(First_);
             !is_null(n) implies ptr_eq(node_.next, return);
             !is_null(n) implies ptr_eq(new_node.next, node.next);
             !is_null(return);


             !is_null(n) implies Seq_Node_to_Seq(First_) == Seq_Cons { head: node.data, tail: Seq_Node_to_Seq(First)}; 
             Seq_Node_to_Seq(Rest) == Seq_Node_to_Seq(Rest_);
             is_null(n) implies flatten(L_) == Seq_Cons{head: element, tail: Seq_Nil{}};
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
