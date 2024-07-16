#include "./headers.h"

struct node *singleton(int element)
/*@ ensures take Ret = Dll_at(return);
        Ret == Dll{left: Seq_Nil{}, n: struct node{data: element, prev: NULL, next: NULL}, right: Seq_Nil{}};
@*/
{
   struct node *n = malloc_node();
   n->data = element;
   n->prev = 0;
   n->next = 0;
   return n;
}