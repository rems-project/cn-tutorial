#include "./headers.h"

/* TODO: I want the spec to say that the first half and the second half of the list 
 * (First and Rest) are the same, there is just an extra node in the middle.
 * Currently the spec is saying the following:

 * When we first call LinkedList(n), we get the first part, the node n points to, 
 * and the rest of the list. When we add a new node and call LinkedList on the new node,
 * the old node is squished into the first part. Then we have the new node and then the 
 * rest of the list stays the same. 
 
 * The first paragraph of specs is making sure all of the pointers are correct. 
 * (TODO: is this already checked through the LinkedList predicate?)
 
 * The second paragraph is making sure that the two halves of the list
 * are the same, except for the new node added to the beginning of First.

 * We have to include in these specs whether or not the given node was null.
 
 * I believe the spec currently is correct, but it is very verbose and hard to understand.
 * I would like to find a simpler version. Maybe even write a correctness function?


 * Maybe something like 
        !is_null(n) implies flatten(L_) == append(rev(Seq_Node_to_Seq(First)), Seq_Cons{head: node.data, tail: Seq_Cons{head: new_node.data, tail: Seq_Node_to_Seq(Rest)}});
         is_null(n) implies flatten(L_) == Seq_Cons{head: element, tail: Seq_Nil{}};

 * But this became very hard to prove with tons of unfolds

*/

//TODO: make first and rest into left and right
//TODO: add D to Lknked list predicate name or OwnedDLL ? or (DLL_at best one rn)
// TODO: get rid of node seq and just use seq on either side

// Adds after the given node and returns a pointer to the new node
struct node *add(int element, struct node *n)
/*@ requires take L = Owned_Dll(n);
             let n_node = Node(L);
             let Left = Left(L);
             let Right = Right(L);
    ensures  take L_ = Owned_Dll(return);
             let new_node = Node(L_);
             is_null(n) ? L_ == Dll { left: Seq_Nil{}, n: new_node, right: Seq_Nil{}}
                        : L_ == Dll { left: Seq_Cons{head: n_node.data, tail: Left}, n: new_node, right: Right};
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