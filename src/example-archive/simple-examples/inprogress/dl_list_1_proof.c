#include <stddef.h>
// #include <stdio.h> 

struct dll_node
{
  int val;
  struct dll_node *next;
  struct dll_node *prev;
};

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons { i32 val, datatype seq next}
}
@*/

/*@ 
// Doubly-linked list predicate based on the separation logic definition here: 
// https://www.comp.nus.edu.sg/~cs6202/slides/08-seplogic_4_in_1.pdf

predicate (datatype seq) DLSeg(pointer i, pointer i_, pointer k, pointer k_) 
{ 
  if (addr_eq(i,k) && addr_eq(i_, k_)) {
    return Seq_Nil{}; 
  } else {
    take H = Owned<struct dll_node>(i); 
    assert (is_null(H.next) || H.next != NULL);
    assert (is_null(H.prev) || H.prev != NULL);
    assert (H.prev == i_); 
    take tl = DLSeg(H.next, i, k, k_); 
    return (Seq_Cons {val: H.val, next: tl }); 
  }
}
@*/

void dll_1step(struct dll_node *curr)
/*@ 
requires 
  take D  = DLSeg(curr, NULL, NULL, NULL);
  let head = curr;  
ensures 
  take D_ = DLSeg(head, NULL, NULL, NULL); 
@*/
{
  if (curr != NULL) {
    curr->val = 7; 
  }
}

void dll_walk_fwd(struct dll_node *head)
/*@ 
requires 
  take D  = DLSeg(head, NULL, NULL, NULL);
ensures 
  take D_ = DLSeg(head, NULL, NULL, NULL); 
@*/
{
  struct dll_node *curr = head; 
  struct dll_node *prev_curr = NULL; 

  while (curr != NULL) 
  /*@ 
  inv 
    take Visited = DLSeg(head, NULL, curr, prev_curr); 
    take Remaining = DLSeg(curr, prev_curr, NULL, NULL); 
    {head}unchanged; 
  @*/
  { 
    // printf("%d ", curr->val); 
    prev_curr = curr; 
    curr->val = 7; // Write an arbitrary value 
    curr = curr->next; 
  }
  return; 
}

void dll_walk_back(struct dll_node *curr)
/*@ trusted; @*/
{
  while (curr != NULL) 
  { 
    // printf("%d ", curr->val); 
    curr = curr->prev; 
  }
  return; 
}

void dll_insert_fwd(struct dll_node *curr, struct dll_node *new, int position)
/*@ trusted; @*/
{
  while (position != 0)
  { 
    position--; 
    curr = curr->next; 
  }; 
  if (curr->next != NULL) {
    curr->next->prev = new; 
  }
  new->prev = curr; 
  new->next = curr->next;  
  curr->next = new; 
}

// int main()
// {
//   struct dll_node n1 = {.val = 1, .prev = NULL};
//   struct dll_node n2 = {.val = 2, .prev = &n1};
//   struct dll_node n3 = {.val = 3, .next = NULL, .prev = &n2};
//   n1.next = &n2; 
//   n2.next = &n3; 

//   printf("Walking a non-empty list forward: [ "); 
//   dll_walk_fwd(&n1); 
//   printf("]\n"); 

//   printf("Walking a non-empty list backward: [ "); 
//   dll_walk_back(&n3); 
//   printf("]\n"); 

//   printf("Walking the empty list: [ ");
//   dll_walk_fwd(NULL); 
//   printf("]\n"); 

//   struct dll_node n4 = {.val = 4};

//   int pos = 1; 
//   printf("Inserting a node at position %d... \n", pos);
//   dll_insert_fwd(&n1, &n4, pos); 

//   printf("Walking a non-empty list forward: [ "); 
//   dll_walk_fwd(&n1); 
//   printf("]\n"); 

//   printf("Walking a non-empty list backward: [ "); 
//   dll_walk_back(&n3); 
//   printf("]\n"); 

//   return 0; 
// }