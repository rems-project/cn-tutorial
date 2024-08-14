#include "./headers.h"

struct node *singleton(int element)
/*@ ensures take Ret = Dll_at(return);
        Ret == Dll{left: Nil{}, curr: struct node{data: element, prev: NULL, next: NULL}, right: Nil{}};
@*/
{
   struct node *n = malloc__node();
   n->data = element;
   n->prev = 0;
   n->next = 0;
   return n;
}