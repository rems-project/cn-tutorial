#include "./headers.h"

struct node *singleton(int element)
/*@ ensures take Ret = LinkedList(return);
        Ret == Dll{first: Seq_Node_Nil{}, n: struct node{data: element, prev: NULL, next: NULL}, rest: Seq_Node_Nil{}};
@*/
{
   struct node *n = malloc_node();
   n->data = element;
   n->prev = 0;
   n->next = 0;
   return n;
}