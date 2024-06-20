#include "../list.h"
#include "../list_length.c"
#include "../list_snoc.h"

struct linkedList {
  struct linkedListCell* front;  
  struct linkedListCell* back;
  unsigned int length;
};

struct linkedListCell {
  int data;  
  struct linkedListCell* prev;
  struct linkedListCell* next;
};

/*@
predicate (datatype seq) LinkedListPtr (pointer l) {
  take L = Owned<struct linkedList>(l);
  assert (   (is_null(L.front)  && is_null(L.back)) 
          || (!is_null(L.front) && !is_null(L.back)));
  take inner = LinkedListFB(L.front, L.back);
  assert ( L.length == length(inner));
  return inner;
}


predicate (datatype seq) LinkedListFB (pointer front, pointer back) {
    if (is_null(front)) {
        return Seq_Nil{};
    } else {
        take B = Owned<struct linkedListCell>(back);
        assert (is_null(B.next));
        take F = Owned<struct linkedListCell>(front);
        assert(is_null(F.prev));
        take L = LinkedListAux (F.next, back);
        return Seq_Cons{ head: F.data, tail: snoc(L, B.data)};
    }
}

predicate (datatype seq) LinkedListAux (pointer f, pointer b) {
    if (ptr_eq(f,b)) {
        return Seq_Nil{};
    } else {
        take F = Owned<struct linkedListCell>(f);
        assert (!is_null(F.next));  
        take B = LinkedListAux(F.next, b);
        return Seq_Cons{head: F.data, tail: B};
    }
}
@*/

extern struct linkedList *mallocLinkedList();
/*@ spec mallocLinkedList();
    requires true;
    ensures take u = Block<struct linkedList>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void freeLinkedList (struct linkedList *p);
/*@ spec freeLinkedList(pointer p);
    requires take u = Block<struct linkedList>(p);
    ensures true;
@*/

extern struct linkedListCell *mallocLinkedListCell();
/*@ spec mallocLinkedListCell();
    requires true;
    ensures take u = Block<struct linkedListCell>(return);
            !is_null(return);
@*/ 

extern void freeLinkedListCell (struct linkedListCell *p);
/*@ spec freeLinkedListCell(pointer p);
    requires take u = Block<struct linkedListCell>(p);
    ensures true;
@*/

struct linkedList* LinkedList_empty ()
/*@ ensures take ret = LinkedListPtr(return);
            ret == Seq_Nil{};
@*/
{
  struct linkedList *p = mallocLinkedList();
  p->front = 0;
  p->back = 0;
  p->length = 0;
  /*@ unfold length(Seq_Nil{}); @*/
  return p;
}

// Given a linked list pointer, inserts a new node
// to the head of the list
void push (struct linkedList* l, int element)
/*@ requires (!is_null(l));
             take L1 = LinkedListPtr(l);
    ensures  take L2 = LinkedListPtr(l);
             L2 == Seq_Cons{head: element, tail: L1};
             length(L2) == length(L1) + 1u32;
@*/
{
    struct linkedListCell *newCell = mallocLinkedListCell();
    newCell->data = element;
    newCell->next = l->front;
    newCell->prev = 0;

    if (l->front != 0) {
        l->front->prev = newCell;
    }

    l->front = newCell;
    l->length = l->length + 1;
}