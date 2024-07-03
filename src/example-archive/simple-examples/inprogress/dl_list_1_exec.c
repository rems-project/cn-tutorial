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

void dll_print_list(struct dll_node* head, struct dll_node* tail)
{
  printf("Forward:  [ "); 
  dll_walk_fwd(head); 
  printf("]\n"); 

  printf("Backward: [ "); 
  dll_walk_back(tail); 
  printf("]\n"); 
}

void dll_insert_pos(struct dll_node *curr, struct dll_node *new, int position)
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

// Modified from code by EAustell 
void dll_insert_ptr_left(struct dll_node *curr, struct dll_node *new){
  if (curr->prev != NULL) {
    curr->prev->next = new;
  }
  new->prev = curr->prev; 
  curr->prev = new;
  new->next = curr; 
}

// Modified from code by by EAustell 
int dll_remove(struct dll_node *n)
{
  if (n->prev == NULL) {  // n is the head
    n->next->prev = NULL;
  } else if (n->next == NULL) { // n is the tail
    n->prev->next = NULL;
  } else {
    struct dll_node *next = n->next;
    struct dll_node *prev = n->prev;

    n->next->prev = prev;
    n->prev->next = next;
  }

  int temp = n->val;
  return temp;
}

int main()
{
  struct dll_node n1 = {.val = 1}; 
  struct dll_node n2 = {.val = 2}; 
  struct dll_node n3 = {.val = 3}; 
  // Extra node for insertion tests
  struct dll_node n4 = {.val = 4};
  struct dll_node n5 = {.val = 5};

  // Build a 3-node list 
  n1.prev = NULL;
  n1.next = &n2; 
  n2.prev = &n1; 
  n2.next = &n3; 
  n3.prev = &n2; 
  n3.next = NULL; 

  // Test dll_walk_fwd / dll_walk_back 
  printf("Walking the test list...\n"); 
  dll_print_list(&n1, &n3);

  printf("Walking an empty list...\n");
  dll_print_list(NULL, NULL);

  // Test dll_insert_pos  
  int pos = 1; // positional insertion 
  printf("Inserting node 4 at position %d... \n", pos);
  dll_insert_pos(&n1, &n4, pos); 
  dll_print_list(&n1, &n3);

  // Test dll_insert_ptr  
  printf("Inserting node 5 before node 2... \n");
  dll_insert_ptr_left(&n2, &n5); 
  dll_print_list(&n1, &n3);

  // Test dll_remove 
  printf("Removing node 2...\n"); 
  dll_remove(&n2); 
  dll_print_list(&n1, &n3);

  return 0; 
}