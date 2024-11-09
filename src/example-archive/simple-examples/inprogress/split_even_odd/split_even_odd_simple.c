/* 
Build instructions: 
- To verify the code:  `cn verify split_even_odd_simple.c` 
- To apply the CN PBT tool to the code:  `cn test split_even_odd_simple.c --output-dir=test_out 
- To build and run the test:  `gcc split_even_odd_simple.c -o split_even_odd_simple -DRUN_TESTS && ./split_even_odd_simple` 
*/

#ifdef RUN_TESTS
#include <stdlib.h>
#include <stdio.h>
#endif 

// List node type 
struct list_node
{
  int val;
  struct list_node *next;
};

/*@
// Predicate defining the list segment in memory 
predicate boolean ListSeg(pointer p, pointer tail) {
  if (ptr_eq(p,tail)) {
    return true; 
  } else {
    take H = Owned<struct list_node>(p);
    take tl = ListSeg(H.next, tail);
    return true;
  }
}

// Extend the list by a single node 
// [list] -> (node) -tail->  
//   ~~>  
// [list] -tail-> 
lemma ListExtend(pointer p, pointer tail)
  requires take l1 = ListSeg(p, tail);
           take v = Owned<struct list_node>(tail);
  ensures take l2 = ListSeg(p, v.next);

// Merge two contiguous lists 
// [list] -mid-> [list] -tail->  
//   ~~>  
// [list] -tail->
lemma ListMerge(pointer p, pointer mid, pointer tail)
  requires take l1 = ListSeg(p, mid);
           take l2 = ListSeg(mid, tail);
  ensures take l3 = ListSeg(p, tail);

// For a non-empty list, shift the node to the beginning 
// -p-> [list] -tail-> (node) -nxt-> 
//   ~~>  
// -p-> (node) -> [list] -nxt-> 
lemma ListSwitch(pointer p, pointer tail)
  requires take List = ListSeg(p, tail);
           take EndNode = Owned<struct list_node>(tail);
           let nxt = tail->next;
  ensures take StartNode_ = Owned<struct list_node>(p);
          take List_ = ListSeg(p->next, nxt);
@*/

// free() for list_node 
void cn_free_sized(void *ptr, unsigned long size);
void free_list_node(struct list_node *node)
/*@
trusted;
requires
  take N = Owned<struct list_node>(node);
@*/
{
#ifdef RUN_TESTS
  free(node); 
#else 
  cn_free_sized(node, sizeof(struct list_node));
#endif 
}

// malloc() for list_node 
void *cn_malloc(unsigned long size);
struct list_node *malloc_list_node()
/*@ 
trusted;
ensures
  take Node_ = Owned<struct list_node>(return);
@*/
{
  struct list_node *ret; 
#ifdef RUN_TESTS 
  ret = malloc(sizeof(struct list_node)); 
#else 
  ret = cn_malloc(sizeof(struct list_node)); 
#endif
  ret->val = 0; 
  ret->next = 0; 
  return ret; 
}

// Input: a linked list of integers starting at *head
// Effect: 
//  - Even-indexed nodes are removed from the list
//  - The function returns a pointer to a new list containing
//    even-indexed nodes 
struct list_node *split_even_odd(struct list_node *head)
/*@
requires
  take Input = ListSeg(head, NULL);
ensures
  take Odds_ = ListSeg({head}@start, NULL);
  take Evens_ = ListSeg(return, NULL);
@*/
{
  struct list_node *evens = malloc_list_node(); 
  struct list_node *evens_last = evens;
  struct list_node *ret = 0; 

  while (head != 0 && head->next != 0)
  /*@
  inv
    take OddsI = ListSeg({head}@start,head);
    take EvensI = ListSeg(evens,evens_last);
    take EvensLast = Owned<struct list_node>(evens_last);
    take RemainingI = ListSeg(head,NULL);
    let prev_head = head;
    let prev_evens = evens_last;
  @*/
  {
    struct list_node *tmp = head->next->next;
    evens_last->next = head->next;
    evens_last = evens_last->next;
    head->next = tmp;
    head = tmp;
    /*@ apply ListExtend({head}@start, prev_head); @*/
    /*@ apply ListExtend(evens, prev_evens); @*/
  };

  evens_last->next = 0;

  /*@ apply ListMerge({head}@start, head, NULL); @*/
  /*@ apply ListSwitch(evens, evens_last); @*/

  ret = evens->next;
  free_list_node(evens);
  return ret;
}

#ifdef RUN_TESTS 
void print_list(struct list_node *list)
/*@
trusted;
@*/
{
  printf("[ ");
  while (list != 0)
  {
    printf("%d ", list->val);
    list = list->next;
  };
  printf("]\n");
}

void split_even_odd_test()
/*@
trusted;
@*/
{
  printf("Testing split_even_odd... \n");

  // Create individual nodes on the stack
  struct list_node node1, node2, node3, node4, node5;

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
  node5.next = 0; // Last node points to NULL

  printf("initial: ");
  print_list(&node1);

  struct list_node *res = split_even_odd(&node1);

  printf("   odds: ");
  print_list(&node1);
  printf("  evens: ");
  print_list(res);
}

int main()
/*@
trusted;
@*/
{
  split_even_odd_test();
}
#endif