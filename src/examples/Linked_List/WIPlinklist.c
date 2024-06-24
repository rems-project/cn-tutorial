// NOTE: look at WIPlinklist2.c for more recent/successful developments.
// This file reasons about a linked list structure with a head and tail pointer.

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
        if (front == back) {
            take F = Owned<struct linkedListCell>(front);
            assert (is_null(F.next));
            assert (is_null(F.prev));
            return Seq_Cons {head: F.data, tail: Seq_Nil{}};
        } else {
            take B = Owned<struct linkedListCell>(back);
            assert (is_null(B.next));
            take F = Owned<struct linkedListCell>(front); //problem if only one element
            assert(is_null(F.prev));
            take L = LinkedListAux (F.next, back);
            return Seq_Cons{ head: F.data, tail: snoc(L, B.data)};
        }
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

predicate (datatype seq) LinkedListPtr_backwards (pointer l) {
  take L = Owned<struct linkedList>(l);
  assert (   (is_null(L.front)  && is_null(L.back)) 
          || (!is_null(L.front) && !is_null(L.back)));
  take inner = LinkedListFB_backwards(L.front, L.back);
  assert ( L.length == length(inner));
  return inner;
}

predicate (datatype seq) LinkedListFB_backwards (pointer front, pointer back) {
    if (is_null(back)) {
        return Seq_Nil{};
    } else {
        take B = Owned<struct linkedListCell>(back);
        assert (is_null(B.next));
        take F = Owned<struct linkedListCell>(front);
        assert(is_null(F.prev));
        take L = LinkedListAux (front, B.prev);
        return Seq_Cons{ head: F.data, tail: snoc(L, B.data)};
    }
}


predicate (datatype seq) LinkedListAux_backwards (pointer f, pointer b) {
    if (ptr_eq(f,b)) {
        return Seq_Nil{};
    } else {
        take B = Owned<struct linkedListCell>(b);
        assert (!is_null(B.prev));  
        take F = LinkedListAux(f, B.prev);
        return snoc(F, B.data);
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

// // Given a linked list pointer, inserts a new node
// // to the head of the list
// void push (struct linkedList* l, int element)
// /*@ requires (!is_null(l));
//              take L1 = LinkedListPtr(l);
//     ensures  take L2 = LinkedListPtr(l);
//              L2 == Seq_Cons{head: element, tail: L1};
//              length(L2) == length(L1) + 1u32;
// @*/
// {
//     struct linkedListCell *newCell = mallocLinkedListCell();
//     newCell->data = element;
//     newCell->next = l->front;
//     newCell->prev = 0;

//     if (l->front != 0) {
//         l->front->prev = newCell;
//     }

//     l->front = newCell;
//     l->length = l->length + 1;
// }


/*@
lemma append_lemma_ll (pointer front, pointer p)
  requires
      take L = LinkedListAux(front, p);
      take P = Owned<struct linkedListCell>(p);
  ensures
      take NewL = LinkedListAux(front, P.next);
      NewL == snoc(L, P.data);
@*/

/*@
lemma snoc_facts (pointer front, pointer back, i32 x)
  requires
      take L = LinkedListAux(front, back);
      take B = Owned<struct linkedListCell>(back);
  ensures
      take NewL = LinkedListAux(front, back);
      take NewB = Owned<struct linkedListCell>(back);
      L == NewL; B == NewB;
      let S = snoc (Seq_Cons{head: x, tail: L}, B.data);
      hd(S) == x;
      tl(S) == snoc (L, B.data);
@*/

// Given a linked list pointer, inserts a new node
// at the end of the list.
void append (struct linkedList* l, int element)
/*@ requires (!is_null(l));
             take L1 = LinkedListPtr(l);
    ensures  take L2 = LinkedListPtr(l);
             L2 == snoc(L1, element);
             length(L2) == length(L1) + 1u32;
@*/
{
    struct linkedListCell *newCell = mallocLinkedListCell();
    newCell->data = element;
    newCell->next = 0;
    newCell->prev = 0;

    // empty list case
    if (l->back == 0) {
        /*@ assert(L1 == Seq_Nil{}); @*/
        l->front = newCell;
        l->back = newCell;
        l->length = l->length + 1;
        /*@ unfold length(Seq_Nil{}); @*/
        /*@ unfold length(Seq_Cons {head: element, tail: Seq_Nil{}}); @*/
        /*@ unfold snoc(L1, element); @*/
        return;
    } else {
        struct linkedListCell *oldback = l->back;
        // l->back->next = newCell;
        l->back = newCell;
        newCell->prev = oldback;
        l->length = l->length + 1;
        /*@ apply append_lemma_ll((*l).front, oldback); @*/
        return;
    }
}