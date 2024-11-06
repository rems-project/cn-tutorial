#include <stdlib.h>
#include <stdio.h>
#include "list_preds.h"

/*@
lemma IntListSeqSnoc(pointer p, pointer tail)
  requires take l1 = IntListSeg(p, tail);
           take v = Owned<struct list_node>(tail);
  ensures take l2 = IntListSeg(p, v.next);
          l2 == append(l1, Seq_Cons { val: v.val, next: Seq_Nil {} });

lemma IntListSeqAppend(pointer p, pointer mid, pointer q)
  requires take l1 = IntListSeg(p, mid);
           take l2 = IntListSeg(mid, q);
  ensures take l3 = IntListSeg(p, q);
          l3 == append(l1, l2);
@*/

void free_list_node_fake(struct list_node *node) 
/*@ 
trusted;
requires 
  take N = Owned<struct list_node>(node); 
@*/
{
  // free(node); // Not needed for stack allocated nodes 
}

void remove_even(struct list_node *head)
/*@
requires
  take Target = IntListSeg(head, NULL);
ensures
  take Result_ = IntListSeg(head, NULL);
@*/
{
  struct list_node *curr = head;

  while (curr != NULL && curr->next != NULL)
  /*@
    inv
      {head} unchanged;
      take Modified = IntListSeg(head,curr);
      take Remaining = IntListSeg(curr,NULL);
      let prev_curr = curr;
  @*/
  {
    struct list_node *tmp = curr->next->next;
    free_list_node_fake(curr->next);
    curr->next = tmp;
    curr = tmp;
    /*@ apply IntListSeqSnoc(head, prev_curr); @*/
  };
  /*@ apply IntListSeqAppend(head, curr, NULL); @*/
  return;
}

struct list_node *list_reverse(struct list_node *head)
/*@ requires take ListPre  = IntListSeg(head, NULL); @*/
/*@ ensures  take ListPost = IntListSeg(return, NULL); @*/
{
  struct list_node *prev, *next, *curr;
  curr = head;

  prev = NULL;
  next = NULL;

  while (curr != NULL)
  /*@ inv take InInv = IntListSeg(curr, NULL);
          take RevInv = IntListSeg(prev, NULL); @*/
  {
    next = curr->next;
    curr->next = prev;
    prev = curr;
    curr = next;
  }
  return prev;
}

struct list_node *split_even_odd_rev(struct list_node *head)
/*@
requires
  take Input = IntListSeg(head, NULL);
ensures
  take Odds_ = IntListSeg({head}@start, NULL);
  take Evens_ = IntListSeg(return, NULL);
@*/
{
  struct list_node *evens = NULL;

  while (head != NULL && head->next != NULL)
  /*@
    inv
      take OddsI = IntListSeg({head}@start,head);
      take RemainingI = IntListSeg(head,NULL);
      take EvensI = IntListSeg(evens,NULL);
      let prev_head = head;
  @*/
  {
    struct list_node *tmp = head->next->next;
    head->next->next = evens;
    evens = head->next;
    head->next = tmp;
    head = tmp;
    /*@ apply IntListSeqSnoc({head}@start, prev_head); @*/
  };
  /*@ apply IntListSeqAppend({head}@start, head, NULL); @*/

  evens = list_reverse(evens);
  return evens;
}

struct list_node *split_even_odd_alt(struct list_node *head)
/*@
trusted; 
@*/
{
  struct list_node evens; 
  struct list_node *evens_head, *evens_tail; 
  evens.next = NULL; 
  evens_tail = &evens; 
  evens_head = evens_tail; 

  while (head != NULL && head->next != NULL)
  {
    struct list_node *tmp = head->next->next;
    head->next->next = NULL;
    evens_tail->next = head->next; 
    evens_tail = evens_tail->next; 
    head->next = tmp;
    head = tmp;
  };

  return evens_head->next;
}

void print_list(struct list_node *list)
/*@
trusted;
@*/
{
  printf("[ ");
  while (list != NULL)
  {
    printf("%d ", list->val);
    list = list->next;
  };
  printf("]\n");
}

void remove_even_test()
/*@
trusted;
@*/
{
  printf("Testing remove_even... \n"); 

  // Create individual nodes on the stack
  struct list_node node1;
  struct list_node node2;
  struct list_node node3;
  struct list_node node4;
  struct list_node node5;

  // Initialize values and set up links between nodes
  node1.val = 1;
  node1.next = &node2;
  node2.val = 2;
  node2.next = &node3;
  node3.val = 3;
  node3.next = &node4;
  node4.val = 4;
  node4.next = &node5;
  node5.val = 5;
  node5.next = NULL; // Last node points to NULL

  printf("initial: ");
  print_list(&node1);

  remove_even(&node1);

  printf(" &node1: ");
  print_list(&node1);
}

void split_even_odd_rev_test()
/*@
trusted;
@*/
{
  printf("Testing split_even_odd_rev... \n"); 

  // Create individual nodes on the stack
  struct list_node node1;
  struct list_node node2;
  struct list_node node3;
  struct list_node node4;
  struct list_node node5;

  // Initialize values and set up links between nodes
  node1.val = 1;
  node1.next = &node2;
  node2.val = 2;
  node2.next = &node3;
  node3.val = 3;
  node3.next = &node4;
  node4.val = 4;
  node4.next = &node5;
  node5.val = 5;
  node5.next = NULL; // Last node points to NULL

  printf("initial: ");
  print_list(&node1);

  struct list_node *res = split_even_odd_rev(&node1);

  printf(" &node1: ");
  print_list(&node1);
  printf("    res: ");
  print_list(res);
}

void split_even_odd_alt_test()
/*@
trusted;
@*/
{
  printf("Testing split_even_odd_alt... \n"); 

  // Create individual nodes on the stack
  struct list_node node1;
  struct list_node node2;
  struct list_node node3;
  struct list_node node4;
  struct list_node node5;

  // Initialize values and set up links between nodes
  node1.val = 1;
  node1.next = &node2;
  node2.val = 2;
  node2.next = &node3;
  node3.val = 3;
  node3.next = &node4;
  node4.val = 4;
  node4.next = &node5;
  node5.val = 5;
  node5.next = NULL; // Last node points to NULL

  printf("initial: ");
  print_list(&node1);

  struct list_node *res = split_even_odd_alt(&node1);

  printf(" &node1: ");
  print_list(&node1);
  printf("    res: ");
  print_list(res);
}

int main() 
/*@ 
trusted; 
@*/
{
  remove_even_test(); 
  printf("\n"); 
  split_even_odd_rev_test(); 
  printf("\n"); 
  split_even_odd_alt_test(); 
}