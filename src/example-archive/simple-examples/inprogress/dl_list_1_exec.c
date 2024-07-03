#include <stddef.h>
#include <stdio.h> 

struct dll_node
{
  int val;
  struct dll_node *next;
  struct dll_node *prev;
};

void dll_walk_fwd(struct dll_node *curr)
{
  while (curr != NULL) 
  { 
    printf("%d ", curr->val); 
    curr = curr->next; 
  }
  return; 
}

void dll_walk_back(struct dll_node *curr)
{
  while (curr != NULL) 
  { 
    printf("%d ", curr->val); 
    curr = curr->prev; 
  }
  return; 
}

void dll_insert_fwd(struct dll_node *curr, struct dll_node *new, int position)
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

int main()
{
  struct dll_node n1 = {.val = 1, .prev = NULL};
  struct dll_node n2 = {.val = 2, .prev = &n1};
  struct dll_node n3 = {.val = 3, .next = NULL, .prev = &n2};
  n1.next = &n2; 
  n2.next = &n3; 

  printf("Walking a non-empty list forward: [ "); 
  dll_walk_fwd(&n1); 
  printf("]\n"); 

  printf("Walking a non-empty list backward: [ "); 
  dll_walk_back(&n3); 
  printf("]\n"); 

  printf("Walking the empty list: [ ");
  dll_walk_fwd(NULL); 
  printf("]\n"); 

  struct dll_node n4 = {.val = 4};

  int pos = 1; 
  printf("Inserting a node at position %d... \n", pos);
  dll_insert_fwd(&n1, &n4, pos); 

  printf("Walking a non-empty list forward: [ "); 
  dll_walk_fwd(&n1); 
  printf("]\n"); 

  printf("Walking a non-empty list backward: [ "); 
  dll_walk_back(&n3); 
  printf("]\n"); 

  return 0; 
}