struct dbl_queue {
  struct node* front;  
  struct node* back;
};

struct node {
  int data;  
  struct node* prev;
  struct node* next;
};