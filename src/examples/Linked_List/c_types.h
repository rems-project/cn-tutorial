struct node {
  int data;  
  struct node* prev;
  struct node* next;
};

struct node_and_int {
  struct node* node;
  int data;
};