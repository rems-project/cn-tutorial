
#include "bst_map.h"
#include "bst_map_cn.h"


#if 0
/* Allocate a new singleton node */
struct MapNode *newNode(KEY key, VALUE value)
/*@
requires
  true;
ensures
  take node = Owned<struct MapNode>(return);
  node.key == key;
  node.value == value;
  is_null(node.smaller);
  is_null(node.larger);
@*/
{
  struct MapNode *node = malloc_MapNode();
  node->key = key;
  node->value = value;
  node->smaller = NULL;
  node->larger = NULL;
  return node;
}
#endif



#if 0
// A no-op function, just shows hows to traverse a tree with a loop.
void traverse(struct MapNode *node)
/*@
requires
  take start = BST(node);
ensures
  take end = BST(node);
  start == end;
@*/
{
  struct MapNode *cur = node;

  /*@ split_case is_null(cur); @*/
  /*@ unfold setKey(fromBSTNode(start).data.key, Leaf {}, start); @*/
  while (cur)
  /*@
  inv
    {node} unchanged;
    take focus = BSTFocus(node,cur);
    start == unfocus(focus);
    let cur_prev = cur;
  @*/
  {
    cur = cur->smaller;
    /*@ apply FocusedGo(node,cur_prev,true); @*/
  }
}
#endif


#if 0
struct MapNode *findLeast(struct MapNode *p)
/*@
requires
  take tree = BST(p);
ensures
  take final_tree = BST(p);
  tree == final_tree;
@*/
{
  struct MapNode *parent = 0;
  struct MapNode *cur = p;
  /*@ split_case is_null(cur); @*/
  /*@ unfold setKey(fromBSTNode(tree).data.key, Leaf {}, tree); @*/
  while(cur)
  /*@
  inv
    {p} unchanged;
    take front = BSTFocus(p,cur);
    tree == unfocus(front);
    let cur_prev = cur;
  @*/
  {
    parent = cur;
    cur = cur->smaller;
     /*@ apply FocusedGoSmaller(p,cur_prev); @*/
  }
  return parent;
}
#endif

#if 1
/* Look for a node and its parent */
struct MapNode *findNode(struct MapNode *root, KEY key)
/*@
requires
  take tree = BST(root);
ensures
  take focus = BSTFocus(root, return);
  unfocus(focus) == tree;
  match focus {
    AtLeaf { tree: _ } => { !member(key,tree) }
    AtNode { done: _, node: node, smaller: _, larger: _ } => {
      node.key == key
    }
  };
@*/
{
  struct MapNode *cur = root;
  /*@ split_case is_null(cur); @*/
  /*@ unfold setKey(fromBSTNode(tree).data.key, Leaf {}, tree); @*/
  /*@ unfold member(key, Leaf {}); @*/
  while (cur)
  /*@ inv
  {root} unchanged;
  {key} unchanged;
  take focus = BSTFocus(root,cur);
  unfocus(focus) == tree;
  !member(key, focusDone(focus));
  let cur_prev = cur;
  @*/
  {
    KEY k = cur->key;
    if (k == key) return cur; 
    cur = k < key? cur->larger : cur->smaller;
    /*@ apply FocusedGoKey(root, cur_prev, k > key, key); @*/
  }
  return 0;
}
#endif


/*@
predicate BSTFocus FindParentFocus(pointer tree_ptr,  pointer cur_ptr, pointer parent_ptr, KEY key) {
  if (is_null(cur_ptr)) {
    take focus = BSTFocus(tree_ptr, parent_ptr);
    let tree_after = unfocus(focus);
    assert(!member(key,tree_after)); // More?
    return focus;
  } else {
    // Found in tree
    take focus = BSTFocus(tree_ptr, cur_ptr);
    let at_node = fromBSTFocusNode(focus);
    assert(at_node.node.key == key);
    return focus;
  }
}
@*/


#if 0
/* Look for a node and its parent */
struct MapNode *findParent(struct MapNode **node, KEY key)
/*@
requires
  take tree_ptr = Owned<struct MapNode*>(node);
  take tree     = BST(tree_ptr);
ensures
  take cur_ptr   = Owned<struct MapNode*>(node);
  let parent_ptr = return;
  take focus     = FindParentFocus(tree_ptr, parent_ptr, cur_ptr, key);
  let tree_after = unfocus(focus);
  tree == tree_after;
@*/
{
  struct MapNode *parent = 0;
  struct MapNode *cur = *node;
  /*@ split_case is_null(cur); @*/
  while (cur)
  /*@ inv
    {node} unchanged;
    {key}  unchanged;
    take node_ptr = Owned<struct MapNode*>(node);
    ptr_eq(node_ptr,tree_ptr);
    take focus = BSTFocus(tree_ptr, cur);
    let cur_prev = cur;
  @*/
{
    KEY k = cur->key;
    if (k == key) {
      *node = cur;
      /*@ split_case is_null(cur); @*/
      return parent;
    }
    parent = cur;
    cur = k < key? cur->larger : cur->smaller;
    /*@ apply FocusedGo(tree_ptr, cur_prev, k > key); @*/
  }
  *node = cur;
  return parent;
}
#endif


#if 0
/* Create an empty set */
struct Map map_empty() 
/*@  @*/
{
  return (struct Map) { .root = NULL };
}
#endif

#if 0
/* Lookup a value in a map */
bool map_lookup(struct Map map, KEY key, VALUE *value) {
  struct MapNode *search = map.root;
  findParent(&search, key);
  if (search == NULL) { return false; }
  *value = search->value;
  return true;
}
#endif

#if 0
/* Insert an element into a map. Overwrites previous if already present. */
void map_insert(struct Map *map, KEY key, VALUE value) {
  struct MapNode *search = map->root;
  struct MapNode *parent = findParent(&search, key);
  if (search != NULL) {
    search->value = value;
    return;
  }

  if (parent == NULL) {
    map->root = newNode(key,value);
    return;
  }

  struct MapNode *new_node = newNode(key,value);
  if (parent->key < key) {
    parent->larger = new_node;
  } else {
    parent->smaller = new_node;
  }
}
#endif
