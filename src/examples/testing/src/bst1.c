#include <stddef.h>


#define KEY    int
#define VALUE  long

struct MapNode {
  KEY key;
  VALUE value; 
  struct MapNode *smaller;
  struct MapNode *larger;
};

extern void* cn_malloc(size_t size);
extern void cn_free_sized(void *ptr, size_t size);


/*@


// *****************************************************************************
//  Keys and Values
// *****************************************************************************

type_synonym KEY      = i32
type_synonym VALUE    = i64
type_synonym NodeData = { KEY key, VALUE value }

function (KEY) defaultKey() { 0i32 }

function (VALUE) defaultValue() { 0i64 }

function (NodeData) defaultNodeData() { 
  {
    key:   defaultKey(),
    value: defaultValue()
  }
}

// Semantic data stored at a node
function (NodeData) getNodeData(struct MapNode node) {
  {
    key:   node.key,
    value: node.value
  }
}

datatype ValueOption {
  ValueNone {},
  ValueSome { VALUE value }
}

function (boolean) isValueSome(ValueOption v) {
  match v {
    ValueNone {}           => { false }
    ValueSome { value: _ } => { true }
  }
}



// *****************************************************************************
// Binary Trees
// *****************************************************************************

// An in-memory binary tree
datatype BSTMem {
  LeafMem {},
  NodeMem {
    struct MapNode data, 
    BSTMem         smaller,
    BSTMem         larger
  }
}

// The values in a binary tree.
datatype BST {
  Leaf {},
  Node {
    NodeData data,
    BST      smaller,
    BST      larger
  }
}

// Describes the layout of an initialized binary tree in memory
predicate BSTMem BSTMem(pointer root) {
  if (is_null(root)) {
    return LeafMem {};
  } else {
    take data     = Owned<struct MapNode>(root);
    take smaller  = BSTMem(data.smaller);
    take larger   = BSTMem(data.larger);
    return
      NodeMem {
        data:    data, 
        smaller: smaller,
        larger:  larger
      };
  }
}

// Forget the pointers for an in-memory tree.
function [rec] (BST) treeValue(BSTMem tree) {
  match tree {
    LeafMem {} => { Leaf {} }
    NodeMem { data: data, smaller: smaller, larger: larger } => {
      Node {
        data:    getNodeData(data),
        smaller: treeValue(smaller),
        larger:  treeValue(larger)
      }
    }
  }
}

function (boolean) isLeaf(BST tree) {
  match tree {
    Leaf {}                                 => { true }
    Node { data: _, smaller: _, larger: _ } => { false }
  }
}







// *****************************************************************************
// Intervals
// *****************************************************************************

// Closed, non-empty interval
type_synonym NonEmptyI = { KEY lower, KEY upper }

// Non-empty, closed intervals
datatype Interval {
  EmptyI {},
  NonEmptyI { NonEmptyI i }
}

function (Interval) defaultInterval() {
  EmptyI {}
}

datatype IntervalOption {
  IntervalNone {},
  IntervalSome { Interval i }
}

function (boolean) isIntervalSome(IntervalOption i) {
  match i {
    IntervalNone {}      => { false }
    IntervalSome { i:_ } => { true }
  }
}

function (Interval) fromIntervalSome(IntervalOption i) {
  match i {
    IntervalNone {}      => { defaultInterval() }
    IntervalSome { i:j } => { j }
  }
}

function (Interval) singletonI(KEY k) {
  NonEmptyI { i: { lower: k, upper: k } }
}

function (IntervalOption) joinIntervals(Interval lower, Interval upper) {
  match lower {
    EmptyI {} => {
      IntervalSome { i: upper }
    }
    NonEmptyI { i: lowerI } => {
      match upper {
        EmptyI {} => {
          IntervalSome { i: lower }
        }
        NonEmptyI { i: upperI } => {
          if (lowerI.upper < upperI.lower) {
            IntervalSome { i: NonEmptyI { i: { lower: lowerI.lower, upper: upperI.upper } } }
          } else {
            IntervalNone {}
          }
        }
      }
    }
  }
}

function (IntervalOption)
  joinIntervalOpt(IntervalOption lowerOpt, IntervalOption upperOpt) {
  match lowerOpt {
    IntervalNone {} => { IntervalNone {} }
    IntervalSome { i: lower } => {
      match upperOpt {
        IntervalNone {} => { IntervalNone {} }
        IntervalSome { i: upper } => {
          joinIntervals(lower,upper)    
        }
      }
    }
  }
}



// *****************************************************************************
// Binary Search Tree
// *****************************************************************************

function [rec] (IntervalOption) bstRange(BST tree) {
  match tree {
    Leaf {} => { IntervalSome { i: EmptyI {} } }
    Node { data: data, smaller: smaller, larger: larger } => {
      let smallerOpt = bstRange(smaller);
      let largerOpt  = bstRange(larger);
      let thisI      = IntervalSome { i: singletonI(data.key) };
      let mid        = joinIntervalOpt(smallerOpt, thisI);
      joinIntervalOpt(mid,largerOpt)
    }
  }
}

function (boolean) validBST(BST tree) {
  isIntervalSome(bstRange(tree))
}

function (boolean) hasRoot(KEY key, BST tree) {
  match tree {
    Leaf {} => { false }
    Node { data: data, smaller: _, larger: _ } => { data.key == key }
  }
}

function [rec] (ValueOption) lookup(KEY key, BST tree) {
  match tree {
    Leaf {} => { ValueNone {} }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (data.key == key) {
        ValueSome { value: data.value }
      } else {
        if (data.key < key) {
          lookup(key,larger)
        } else {
          lookup(key,smaller)
        }
      }
    }
  }
}

function (boolean) member(KEY k, BST tree) {
  isValueSome(lookup(k,tree))
}

function [rec] (BST) insert(KEY key, VALUE value, BST tree) {
  match tree {
    Leaf {} => {
      Node {
        data:    { key: key, value: value },
        smaller: Leaf {},
        larger:  Leaf {}
      }
    }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (data.key == key) {
        Node {
          data:    { key: key, value: value },
          smaller: smaller,
          larger:  larger
        }
      } else {
        if (data.key < key) {
          Node {
            data:    data,
            smaller: smaller,
            larger:  insert(key,value,larger)
          }
        } else {
          Node {
            data:    data,
            smaller: insert(key,value,smaller),
            larger:  larger
          }
        }
      }
    }
  }
}


function [rec] ({ NodeData data, BST tree }) delLeast(BST root) {
  match root {
    Leaf {} => {
      {
        data: defaultNodeData(),
        tree: Leaf {}
      }
    }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (isLeaf(smaller)) {
        {
          data: data,
          tree: larger
        }
      } else {
         let res = delLeast(smaller);
         {
           data: res.data,
           tree:
             Node {
               data:    data,
               smaller: res.tree,
               larger:  larger
             }
         }
      }
    }
  }
}

function [rec] (BST) delKey(KEY key, BST root) {
  match root {
    Leaf {} => { Leaf {} }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (key == data.key) {
        let res = delLeast(larger);
        if (isLeaf(res.tree)) {
          smaller
        } else {
          Node {
            data:    res.data,
            smaller: smaller,
            larger:  res.tree
          }
        }
      } else {
        if (key < data.key) {
          Node {
            data:    data,
            smaller: delKey(key, smaller),
            larger:  larger
          }
        } else {
          Node {
            data:    data,
            smaller: smaller,
            larger:  delKey(key, larger)
          }
        }
      }
    }
  }
}

// Retruns `LeafMem` if the pointer is not a node in the tree.
function [rec] (BSTMem) findNode(pointer tgt, pointer tree_ptr, BSTMem tree) {
  if (ptr_eq(tgt,tree_ptr)) {
    tree
  } else {
    match tree {
      LeafMem {} => { tree }
      NodeMem { data: data, smaller: smaller, larger: larger } => {
        let inSmaller = findNode(tgt, data.smaller, smaller);
        match inSmaller {
          LeafMem {} => { findNode(tgt, data.larger, larger) }
          NodeMem { data: _, smaller: _, larger: _ } => { inSmaller } 
        } 
      }
    }
  }
}


@*/





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
  struct MapNode *node = (struct MapNode*)cn_malloc(sizeof(struct MapNode));
  node->key = key;
  node->value = value;
  node->smaller = 0;
  node->larger = 0;
  return node;
}


struct MapNode *findParent(struct MapNode **node, KEY key)
/*@
requires
  take tree_ptr = Owned<struct MapNode*>(node);
  take mem_tree = BSTMem(tree_ptr);
  let tree = treeValue(mem_tree);
  validBST(tree);
ensures
  take new_mem_tree = BSTMem(tree_ptr);
  new_mem_tree == mem_tree;
  take cur_ptr = Owned<struct MapNode*>(node);  
  let parent_node = findNode(return, tree_ptr, mem_tree);
  match parent_node {
    LeafMem {} => {
      isLeaf(tree) && is_null(cur_ptr) ||
      hasRoot(key, tree) && ptr_eq(cur_ptr,tree_ptr)
    }
    NodeMem { data: parent, smaller: smaller, larger: larger } => {
      let tgt =
        if (key < parent.key) {
          { ptr: parent.smaller, tree: smaller } 
        } else {
          { ptr: parent.larger, tree: larger }
        };
      let tgtTree = treeValue(tgt.tree);
      ptr_eq(cur_ptr,tgt.ptr) && (isLeaf(tgtTree) || hasRoot(key,tgtTree))
    }
  };
@*/
{
  struct MapNode *parent = 0;
  struct MapNode *cur = *node;
  while (cur)
  {
    KEY k = cur->key;
    if (k == key) {
      *node = cur;
      return parent;
    }
    parent = cur;
    cur = k < key? cur->larger : cur->smaller;
  }
  *node = cur;
  return parent;
}

#if 0
/* Insert an element into a map. Overwrites previous if already present. */
void setNodeKey(struct MapNode **root, KEY key, VALUE value)
/*
requires
  take root_ptr = Owned(root);
  take tree = BST(root_ptr);
ensures
  take new_root = Owned(root);
  take new_tree = BST(new_root);
  new_tree == insert(key, value, tree);
*/
{
  struct MapNode *found = *root;
  struct MapNode *parent = findParent(&found, key);


  if (found) {
    found->value = value;
    return;
  }

  if (!parent) {
    *root = newNode(key,value);
    return;
  }

  struct MapNode *new_node = newNode(key,value);
  if (parent->key < key) {
    parent->larger = new_node;
  } else {
    parent->smaller = new_node;
  }
}


void deleteTree(struct MapNode *root)
/*
  requires
    take tree = BST(root);
  ensures
     true;
*/
{
  if (!root) return;
  deleteTree(root->smaller);
  deleteTree(root->larger);
  cn_free_sized(root, sizeof(struct MapNode));
}


/*
predicate (void) DeleteSmallest(pointer cur, NodeData data) {
  if (is_null(cur)) {
    return;
  } else {
    take node = Owned<struct MapNode>(cur);
    assert(node.key == data.key);
    assert(node.value == data.value);
    return;
  }
}
*/

struct MapNode* deleteSmallest(struct MapNode **root)
/*
  requires
    take root_ptr = Owned(root);
    take tree = BST(root_ptr);
  ensures
    take new_root = Owned(root);
    take new_tree = BST(new_root);
    let res = delLeast(tree);
    new_tree == res.tree;
    take unsued = DeleteSmallest(return, res.data);    
*/
{
  struct MapNode *cur = *root;
  if (!cur) return 0;

  struct MapNode *parent = 0;
  while (cur->smaller) {
    parent = cur;
    cur = cur->smaller;
  }

  if (parent) parent->smaller = cur->larger;
  //!//
  else *root = cur->larger;
  //!! forget_to_update_root //
  //!//

  return cur;
}


void deleteKey(struct MapNode **root, KEY key)
/*
requires
  take root_ptr = Owned(root);
  take tree = BST(root_ptr);
ensures
  take new_ptr = Owned(root);
  take new_tree = BST(new_ptr);
  delKey(key, tree) == new_tree;
*/
{
  struct MapNode *found = *root;
  struct MapNode *parent = findParent(&found, key);

  if (!found) return;
  struct MapNode *remove = deleteSmallest(&found->larger);
  if (remove) {
    found->key = remove->key;
    found->value = remove->value;    
  } else {
    remove = found;
    //!//
    if (parent) parent->smaller = found->smaller;
    else
    //!! always_update_root_instead_of_parent //
    //!//
      *root = found->smaller;
  }
  cn_free_sized(remove, sizeof(struct MapNode));
}
#endif