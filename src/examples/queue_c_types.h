struct int_queue {
  struct int_queueCell* front;  
  struct int_queueCell* back;
};

struct int_queueCell {
  int first;  
  struct int_queueCell* next;
};
