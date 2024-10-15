
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
// Demonstrates a recursive traversal of a tree.
size_t count(struct MapNode const *node)
/*@
requires
  take before = BST(node);
ensures
  take after = BST(node);
  before == after;
@*/
{
  if (node == NULL) return 0;
  return (size_t)1 + count(node->smaller) + count(node->larger);
}
#endif


#if 1
// A no-op function, just shows hows to traverse a tree with a loop.
void traverse(struct MapNode *node)
/*@
requires
  take start = BST(node, anyKey());
ensures
  take end = BST(node, anyKey());
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
    take focus = BSTFocus(node,cur,anyKey());
    start == unfocus(focus);
    let cur_prev = cur;
  @*/
  {
    cur = cur->smaller;
    /*@ apply GoSmaller(node,cur_prev,anyKey()); @*/
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
  struct MapNode *parent = NULL;
  struct MapNode *cur = p;
  while(cur != NULL)
  /*@
  inv
    {p} unchanged;
    take front = BSTUpTo(cur,parent);
  @*/
  {
    parent = cur;
    cur = p->smaller;
    
  }
  return parent;
}
#endif


#if 0
/* Look for a node and its parent */
struct MapNode *findParent(struct MapNode **node, KEY key)
{
  struct MapNode *parent = NULL;
  struct MapNode *cur = *node;
  while (cur != NULL)
  {
    KEY k = cur->key;
    if (k == key) { *node = cur; return parent; }
    parent = cur;
    cur = k < key? cur->larger : cur->smaller;
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
