#include "./headers.h"

/* TODO: correctness checks.

 * Currently, the correctness check says that either the first part or the last part
 * of the list is unchanged. We don't know which, because the function might return a
 * pointer to the element before or after the removed node.

 * We go through the cases for if it's the first part or the second part that we are
 * pointing to, and say that the other part must have a node removed.
 
 * The last spec says that either the first part has one less element, the second part has one
 * less element, or the list was singleton and so the first and second parts were both empty.

 * Currently, I believe the check is correct however it is very verbose and confusing.
 * I would like to find a simpler version. Maybe even write a correctness function?
*/


// removes the given node from the list and returns another pointer 
// to somewhere in the list, or a null pointer if the list is empty.
struct node_and_int *remove(struct node *n)
/*@ requires !is_null(n);
             take del = Owned<struct node>(n);
             take First = Own_Backwards(del.prev, n, del);
             take Rest = Own_Forwards(del.next, n, del);
    ensures  take ret = Owned<struct node_and_int>(return);
             take L = Owned_Dll(ret.node);
             let First_ = Left(L);
             let Rest_ = Right(L);
             let node = Node(L);
             First_ == First || Rest_ == Rest;
             !is_null(ret.node) implies (First_ == First implies Rest == Seq_Cons{head: node.data, tail: Rest_});

             !is_null(ret.node) implies (Rest_  == Rest implies First == Seq_Cons{head: node.data, tail: First_});

             First == Seq_Cons{head: node.data, tail: First_} || Rest == Seq_Cons{head: node.data, tail: Rest_} || (First == Seq_Nil{} && Rest == Seq_Nil{});

            //  flatten(l) == append(rev(nodeSeqtoSeq(first)), nodeSeqtoSeq(rest));

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