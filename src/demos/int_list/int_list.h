#ifndef __INT_LIST_H__
#define __INT_LIST_H__

typedef struct int_list
{
    int head;
    struct int_list *tail;
} int_list;

/*@
    datatype seq {
        Seq_Nil {},
        Seq_Cons {i32 head, datatype seq tail}
    }

    predicate (datatype seq) IntList(pointer p) {
        if (is_null(p)) {
            return Seq_Nil{};
        } else {
            take H = Owned<struct int_list>(p);
            take tl = IntList(H.tail);
            return (Seq_Cons { head: H.head, tail: tl });
        }
    }
 @*/

int_list *malloc_int_list_node();
/*@ spec malloc_int_list_node();
    requires true;
    ensures take u = Block<int_list>(return);
@*/

void free_int_list_node(int_list *p);
/*@ spec free_int_list_node(pointer p);
    requires take u = Block<int_list>(p);
    ensures true;
@*/

int_list *int_list_new(int head);
/*@ spec int_list_new(i32 head);
    requires true;
    ensures take out = IntList(return);
@*/

#endif
