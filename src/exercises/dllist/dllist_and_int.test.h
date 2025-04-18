struct dllist_and_int {
  struct dllist* dllist;
  int data;
};

struct dllist_and_int *malloc__dllist_and_int()
/*@ ensures take R = W<struct dllist_and_int>(return); @*/
{
  return cn_malloc(sizeof(struct dllist_and_int));
}

void free__dllist_and_int (struct dllist_and_int *p)
/*@ requires take P = W<struct dllist_and_int>(p); @*/
{
  cn_free_sized(p, sizeof(struct dllist_and_int));
}
