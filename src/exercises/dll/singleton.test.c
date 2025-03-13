#include "./headers.test.h"

struct dllist *singleton(int element)
/*@ ensures take Ret = Dll_at(return);
        Ret == Nonempty_Dll {
                 left: Nil{}, 
                 curr: struct dllist {prev: NULL, 
                                      data: element, 
                                      next: NULL}, 
                 right: Nil{}};
@*/
{
   struct dllist *n = malloc__dllist();
   n->data = element;
   n->prev = 0;
   n->next = 0;
   return n;
}
