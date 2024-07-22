// Defines C functions that initialize or data insert for the Binary Tree data structure
// Also gives each function their own associating CN verification

struct TreeNode* TreeNode_nil()
/*@ ensures take ret = IntTree(return);
            ret == Tree_Nil{};
 @*/
{
  return 0;
}

struct TreeNode* TreeNode_cons_left(int val, struct TreeNode* left_b)
/*@ requires take l_b = IntTree(left_b);
    (l_b == Tree_Nil{} || get_data(l_b) < val);
    ensures take ret = IntTree(return);
            ret == Tree_Cons{left: l_b, data: val, right: Tree_Nil{}};
 @*/
{
  struct TreeNode *p = mallocTreeNode();
  p->data = val;
  p->left = left_b;
  p->right = 0;
  return p;
}

struct TreeNode* TreeNode_cons_right(int val, struct TreeNode* right_b)
/*@ requires take r_b = IntTree(right_b);
    (r_b == Tree_Nil{} || get_data(r_b) >= val);
    ensures take ret = IntTree(return);
            ret == Tree_Cons{left: Tree_Nil{}, data: val, right: r_b};
 @*/
{
  struct TreeNode *p = mallocTreeNode();
  p->data = val;
  p->left = 0;
  p->right = right_b;
  return p;
}

struct TreeNode* TreeNode_cons_both(int val, struct TreeNode* left_b, struct TreeNode* right_b)
/*@ requires take l_b = IntTree(left_b);
             take r_b = IntTree(right_b);
             (l_b == Tree_Nil{} || get_data(l_b) < val) && (r_b == Tree_Nil{} || get_data(r_b) >= val);
    ensures take ret = IntTree(return);
            ret == Tree_Cons{left: l_b, data: val, right: r_b};
@*/
{
  struct TreeNode *p = mallocTreeNode();
  p->data = val;
  p->left = left_b;
  p->right = right_b;
  return p;
}