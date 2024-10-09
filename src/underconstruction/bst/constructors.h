// Constructors for trees

struct node* node_nil()
/*@ ensures take Ret = Tree_At(return);
            Ret == Leaf{};
 @*/
{
  return 0;
}

struct node* node_cons_left(int val, struct node* left_b)
/*@ requires take L = Tree_At(left_b);
             (L == Leaf{} || Data_Of(L) < val);
    ensures take Ret = Tree_At(return);
            Ret == Node{Left: L, Data: val, Right: Leaf{}};
 @*/
{
  struct node *t = malloc_node();
  t->data = val;
  t->left = left_b;
  t->right = 0;
  return t;
}

struct node* node_cons_right(int val, struct node* right_b)
/*@ requires take R = Tree_At(right_b);
             (R == Leaf{} || Data_Of(R) >= val);
    ensures take Ret = Tree_At(return);
            Ret == Node{Left: Leaf{}, Data: val, Right: R};
 @*/
{
  struct node *t = malloc_node();
  t->data = val;
  t->left = 0;
  t->right = right_b;
  return t;
}

struct node* node_cons_both(int val, struct node* left_b, struct node* right_b)
/*@ requires take L = Tree_At(left_b);
             take R = Tree_At(right_b);
             (L == Leaf{} || Data_Of(L) < val);
             (R == Leaf{} || Data_Of(R) >= val);
    ensures take Ret = Tree_At(return);
            Ret == Node{Left: L, Data: val, Right: R};
@*/
{
  struct node *t = malloc_node();
  t->data = val;
  t->left = left_b;
  t->right = right_b;
  return t;
}
