// #include <stdlib.h>
// #include "list_preds.h"

// A struct representing nodes from a linked list of integers
struct list_node
{
  int val;
  struct list_node *next;
};

// The specification-level type definition for a sequence. We use this to
// represent the contents of the list.

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons { i32 val, datatype seq next}
}
@*/

// The predicate representing an in-memory list segment. Note that the return
// value of this predicate is the specification-level contents of the list, i.e
// a pure sequence of values.

/*@
predicate (datatype seq) ListSeg(pointer p, pointer tail) {
  if (ptr_eq(p,tail)) {
    return Seq_Nil{};
  } else {
    take H = Owned<struct list_node>(p);
    take tl = ListSeg(H.next, tail);
    return (Seq_Cons { val: H.val, next: tl });
  }
}
@*/

// This append function exists at the specification level

/*@
function [rec] (datatype seq) append(datatype seq xs, datatype seq ys) {
  match xs {
    Seq_Nil {} => {
      ys
    }
    Seq_Cons {val : h, next : zs}  => {
      Seq_Cons {val: h, next: append(zs, ys)}
    }
  }
}
@*/

/*@
lemma ListExtend(pointer p, pointer tail)
  requires take l1 = ListSeg(p, tail);
           take v = Owned<struct list_node>(tail);
  ensures take l2 = ListSeg(p, v.next);
          l2 == append(l1, Seq_Cons { val: v.val, next: Seq_Nil {} });

lemma ListMerge(pointer p, pointer mid, pointer q)
  requires take l1 = ListSeg(p, mid);
           take l2 = ListSeg(mid, q);
  ensures take l3 = ListSeg(p, q);
          l3 == append(l1, l2);
@*/

void cn_free_sized(void *ptr, unsigned long size);

void free_list_node(struct list_node *node)
/*@
trusted;
requires
  take N = Owned<struct list_node>(node);
@*/
{
  cn_free_sized(node, sizeof(struct list_node));
}

void *cn_malloc(unsigned long size);

struct list_node *malloc_list_node()
/*@ 
trusted;
ensures
  take N_ = Owned<struct list_node>(return);
@*/
{
  struct list_node *ret = cn_malloc(sizeof(struct list_node)); 
  ret->val = 0; ret->next = 0; 
  return ret; 
}

void remove_even(struct list_node *head)
/*@
requires
  take Target = ListSeg(head, NULL);
ensures
  take Result_ = ListSeg(head, NULL);
@*/
{
  struct list_node *curr = head;

  while (curr != 0 && curr->next != 0)
  /*@
    inv
      {head} unchanged;
      take Modified = ListSeg(head,curr);
      take Remaining = ListSeg(curr,NULL);
      let prev_curr = curr;
  @*/
  {
    struct list_node *tmp = curr->next->next;
    free_list_node(curr->next);
    curr->next = tmp;
    curr = tmp;
    /*@ apply ListExtend(head, prev_curr); @*/
  };
  /*@ apply ListMerge(head, curr, NULL); @*/
  return;
}

struct list_node *list_reverse(struct list_node *head)
/*@ requires take ListPre  = ListSeg(head, NULL); @*/
/*@ ensures  take ListPost = ListSeg(return, NULL); @*/
{
  struct list_node *prev, *next, *curr;
  curr = head;

  prev = 0;
  next = 0;

  while (curr != 0)
  /*@ inv take InInv = ListSeg(curr, NULL);
          take RevInv = ListSeg(prev, NULL); @*/
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
  take Input = ListSeg(head, NULL);
ensures
  take Odds_ = ListSeg({head}@start, NULL);
  take Evens_ = ListSeg(return, NULL);
@*/
{
  struct list_node *evens = 0;

  while (head != 0 && head->next != 0)
  /*@
    inv
      take OddsI = ListSeg({head}@start,head);
      take RemainingI = ListSeg(head,NULL);
      take EvensI = ListSeg(evens,NULL);
      let prev_head = head;
  @*/
  {
    struct list_node *tmp = head->next->next;
    head->next->next = evens;
    evens = head->next;
    head->next = tmp;
    head = tmp;
    /*@ apply ListExtend({head}@start, prev_head); @*/
  };
  /*@ apply ListMerge({head}@start, head, NULL); @*/

  evens = list_reverse(evens);
  return evens;
}

struct list_node *split_even_odd_alt(struct list_node *head)
/*@
trusted;
requires
  take Input = ListSeg(head, NULL);
ensures
  take Odds_ = ListSeg({head}@start, NULL);
  take Evens_ = ListSeg(return, NULL);
@*/
{
  struct list_node evens, *evens_tail;
  evens.next = 0;
  evens_tail = &evens;

  while (head != 0 && head->next != 0)
  {
    struct list_node *tmp = head->next->next;
    head->next->next = 0;
    evens_tail->next = head->next;
    evens_tail = evens_tail->next;
    head->next = tmp;
    head = tmp;
  };

  return evens.next;
}

/*@
lemma ListNonEmpSwitch(pointer p, pointer tail)
  requires take List = ListSeg(p, tail);
          take EndNode = Owned<struct list_node>(tail);
          let nxt = tail->next;
  ensures take StartNode_ = Owned<struct list_node>(p);
          take List_ = ListSeg(p->next,nxt);
@*/

void split_even_odd_alt_2_helper(struct list_node *head, struct list_node *evens)
/*@
trusted;
requires
  take Input = ListSeg(head, NULL);
  take EvensHead = Owned(evens);
ensures
  take Input_ = ListSeg({head}@start, NULL);
  take EvensHead_ = Owned<struct list_node>({evens}@start);
  take Evens_ = ListSeg({evens}@start->next, NULL);
@*/
{
  while (head != 0 && head->next != 0)
  /*@
  inv
    take OddsI = ListSeg({head}@start,head);
    take EvensI = ListSeg({evens}@start,evens);
    take EvensLast = Owned<struct list_node>(evens);
    take RemainingI = ListSeg(head,NULL);
    let prev_head = head;
    let prev_evens = evens;
  @*/
  {
    struct list_node *tmp = head->next->next;
    evens->next = head->next;
    evens = evens->next;
    head->next = tmp;
    head = tmp;
    /*@ apply ListExtend({head}@start, prev_head); @*/
    /*@ apply ListExtend({evens}@start, prev_evens); @*/
  };

  evens->next = 0;

  /*@ apply ListMerge({head}@start, head, NULL); @*/
  /*@ apply ListNonEmpSwitch({evens}@start, evens); @*/
}

struct list_node *split_even_odd_alt_2(struct list_node *head)
/*@
requires
  take Input = ListSeg(head, NULL);
ensures
  take Odds_ = ListSeg({head}@start, NULL);
  take Evens_ = ListSeg(return, NULL);
@*/
{
  struct list_node evens;
  evens.next = 0;
  evens.val = 0;

  split_even_odd_alt_2_helper(head, &evens);

  return evens.next;
}

struct list_node *split_even_odd_alt_3(struct list_node *head)
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
    take EvensLast = Owned<struct list_node>(evens_last);
    take EvensI = ListSeg(evens,evens_last);
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
  /*@ apply ListNonEmpSwitch(evens, evens_last); @*/

  ret = evens->next;
  free_list_node(evens);
  return ret;
}

// struct list_node *split_even_odd_clean(struct list_node *head)
// /*@ trusted; @*/
// {
//   struct list_node *evens = cn_malloc(sizeof(struct list_node));
//   struct list_node *evens_last = evens;

//   while (head != 0 && head->next != 0)
//   {
//     struct list_node *tmp = head->next->next;
//     evens_last->next = head->next;
//     evens_last = evens_last->next;
//     head->next = tmp;
//     head = tmp;
//   };
//   evens_last->next = 0;

//   struct list_node *ret = evens->next;
//   cn_free_sized(evens, sizeof(struct list_node));
//   return ret;
// }

// #include <stdio.h>

// void print_list(struct list_node *list)
// /*@
// trusted;
// @*/
// {
//   printf("[ ");
//   while (list != NULL)
//   {
//     printf("%d ", list->val);
//     list = list->next;
//   };
//   printf("]\n");
// }

// void remove_even_test()
// /*@
// trusted;
// @*/
// {
//   printf("Testing remove_even... \n");

//   // Create individual nodes on the stack
//   struct list_node node1;
//   struct list_node node2;
//   struct list_node node3;
//   struct list_node node4;
//   struct list_node node5;

//   // Initialize values and set up links between nodes
//   node1.val = 1;
//   node1.next = &node2;
//   node2.val = 2;
//   node2.next = &node3;
//   node3.val = 3;
//   node3.next = &node4;
//   node4.val = 4;
//   node4.next = &node5;
//   node5.val = 5;
//   node5.next = NULL; // Last node points to NULL

//   printf("initial: ");
//   print_list(&node1);

//   remove_even(&node1);

//   printf(" &node1: ");
//   print_list(&node1);
// }

// void split_even_odd_rev_test()
// /*@
// trusted;
// @*/
// {
//   printf("Testing split_even_odd_rev... \n");

//   // Create individual nodes on the stack
//   struct list_node node1;
//   struct list_node node2;
//   struct list_node node3;
//   struct list_node node4;
//   struct list_node node5;

//   // Initialize values and set up links between nodes
//   node1.val = 1;
//   node1.next = &node2;
//   node2.val = 2;
//   node2.next = &node3;
//   node3.val = 3;
//   node3.next = &node4;
//   node4.val = 4;
//   node4.next = &node5;
//   node5.val = 5;
//   node5.next = NULL; // Last node points to NULL

//   printf("initial: ");
//   print_list(&node1);

//   struct list_node *res = split_even_odd_rev(&node1);

//   printf(" &node1: ");
//   print_list(&node1);
//   printf("    res: ");
//   print_list(res);
// }

// void split_even_odd_alt_test()
// /*@
// trusted;
// @*/
// {
//   printf("Testing split_even_odd_alt... \n");

//   // Create individual nodes on the stack
//   struct list_node node1;
//   struct list_node node2;
//   struct list_node node3;
//   struct list_node node4;
//   struct list_node node5;

//   // Initialize values and set up links between nodes
//   node1.val = 1;
//   node1.next = &node2;
//   node2.val = 2;
//   node2.next = &node3;
//   node3.val = 3;
//   node3.next = &node4;
//   node4.val = 4;
//   node4.next = &node5;
//   node5.val = 5;
//   node5.next = NULL; // Last node points to NULL

//   printf("initial: ");
//   print_list(&node1);

//   struct list_node *res = split_even_odd_alt(&node1);

//   printf(" &node1: ");
//   print_list(&node1);
//   printf("    res: ");
//   print_list(res);
// }

// int main()
// /*@
// trusted;
// @*/
// {
//   remove_even_test();
//   printf("\n");
//   split_even_odd_rev_test();
//   printf("\n");
//   split_even_odd_alt_test();
// }