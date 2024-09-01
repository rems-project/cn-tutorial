// Defines C functions that initialize or data insert for the Binary Tree data structure
// Also gives each function their own associating CN verification

struct node* node_nil()
/*@ ensures take ret = Tree_At(return);
            ret == Leaf{};
 @*/
{
  return 0;
}

struct node* node_cons_left(int val, struct node* left_b)
/*@ requires take l_b = Tree_At(left_b);
    (l_b == Leaf{} || get_data(l_b) < val);
    ensures take ret = Tree_At(return);
            ret == Node{Left: l_b, data: val, right: Leaf{}};
 @*/
{
  struct node *p = malloc_node();
  p->data = val;
  p->left = left_b;
  p->right = 0;
  return p;
}

struct node* node_cons_right(int val, struct node* right_b)
/*@ requires take r_b = Tree_At(right_b);
    (r_b == Leaf{} || get_data(r_b) >= val);
    ensures take ret = Tree_At(return);
            ret == Node{Left: Leaf{}, data: val, right: r_b};
 @*/
{
  struct node *p = malloc_node();
  p->data = val;
  p->left = 0;
  p->right = right_b;
  return p;
}

struct node* node_cons_both(int val, struct node* left_b, struct node* right_b)
/*@ requires take l_b = Tree_At(left_b);
             take r_b = Tree_At(right_b);
             (l_b == Leaf{} || get_data(l_b) < val) && (r_b == Leaf{} || get_data(r_b) >= val);
    ensures take ret = Tree_At(return);
            ret == Node{Left: l_b, data: val, right: r_b};
@*/
{
  struct node *p = malloc_node();
  p->data = val;
  p->left = left_b;
  p->right = right_b;
  return p;
}