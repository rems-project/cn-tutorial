#ifndef BST_MAP_CN_H
#define BST_MAP_CN_H

#include "bst_map.h"
#include "bst_sem_cn.h"

// Specialized `malloc`
extern struct MapNode *malloc_MapNode();
/*@
spec malloc_MapNode();
requires
  true;
ensures
  take v = Block<struct MapNode>(return);
@*/



/*@

// *****************************************************************************
// Consuming an entire tree
// *****************************************************************************


// Semantic data stored at a node
function (NodeData) getNodeData(struct MapNode node) {
  { key: node.key, value: node.value }
}


// A binary search tree, where all keys are in the given range.
predicate BST BST(pointer root, Interval range) {
  if (is_null(root)) {
    return Leaf {};
  } else {
    take node = Owned<struct MapNode>(root);
    let data = getNodeData(node);
    assert(inInterval(node.key, range));
    let ranges = splitInterval(node.key, range);
    take smaller = BST(node.smaller, ranges.lower);
    take larger  = BST(node.larger, ranges.upper);
    return Node { data: data, smaller: smaller, larger: larger };
  }
}




// *****************************************************************************
// Focusing on a node in the tree
// *****************************************************************************

type_synonym BSTNodeFocus =
  { BST done, struct MapNode node, BST smaller, BST larger }

datatype BSTFocus {
  AtLeaf { BST tree },
  AtNode { BST done, struct MapNode node, BST smaller, BST larger }
}

// Access focus data, when we already know that we are at a node.
function (BSTNodeFocus) fromBSTFocusNode(BSTFocus focus) {
  match focus {
    AtLeaf { tree: _ } => { default<BSTNodeFocus> }
    AtNode { done: done, node: node, smaller: smaller, larger: larger } => {
      { done: done, node: node, smaller: smaller, larger: larger }
    }
  }
}

predicate BSTFocus BSTFocus(pointer root, pointer child, Interval range) {
  if (is_null(child)) {
    take tree = BST(root, range);
    return AtLeaf { tree: tree };
  } else {
    take node    = Owned<struct MapNode>(child);
    take result  = BSTNodeUpTo(root, child, node, range);
    let ranges   = splitInterval(node.key,result.range);
    take smaller = BST(node.smaller, ranges.lower);
    take larger  = BST(node.larger, ranges.upper);
    return AtNode { done: result.tree, node: node,
                    smaller: smaller, larger: larger };
  }
}

// Consume parts of the tree starting at `p` until we get to `c`.
// We do not consume `c`.
// `child` is the node stored at `c`.
predicate { BST tree, Interval range }
  BSTNodeUpTo(pointer p, pointer c, struct MapNode child, Interval range) {
  if (ptr_eq(p,c)) {
    return { tree: Leaf {}, range: range };
  } else {
    take parent = Owned<struct MapNode>(p);
    assert(inInterval(parent.key, range));
    let ranges = splitInterval(parent.key, range);
    take result = BSTNodeChildUpTo(c, child, parent, ranges);
    return result;
  }
}

// Starting at a parent with data `data` and children `smaller` and `larger`,
// we go toward `c`, guided by its value, `target`.
predicate { BST tree, Interval range }
  BSTNodeChildUpTo(pointer c, struct MapNode target, struct MapNode parent, Intervals ranges) {
  if (parent.key < target.key) {
    take small = BST(parent.smaller, ranges.lower);
    take large = BSTNodeUpTo(parent.larger, c, target, ranges.upper);
    return { tree: Node { data: getNodeData(parent), smaller: small, larger: large.tree },
             range: large.range };
  } else {
  if (parent.key > target.key) {
    take small = BSTNodeUpTo(parent.smaller, c, target, ranges.lower);
    take large = BST(parent.larger, ranges.upper);
    return { tree: Node { data: getNodeData(parent), smaller: small.tree, larger: large },
             range: small.range };
  } else {
    // We should never get here, but asserting `false` is not allowed
    return default<{ BST tree, Interval range }>;
  }}
}

function (BST) unfocus(BSTFocus focus) {
  match focus {
    AtLeaf { tree: tree } => { tree }
    AtNode { done: tree, node: node, smaller: smaller, larger: larger } => {
      let bst = Node { data: getNodeData(node), smaller: smaller, larger: larger };
      setKey(node.key, tree, bst)  
    }
  }
}



lemma GoSmaller(pointer root, pointer cur, Interval range)
  requires
    !is_null(cur);
    take focus = BSTFocus(root,cur,range);
  ensures
    let node = fromBSTFocusNode(focus).node;
    take focus_smaller = BSTFocus(root,node.smaller,range);
    unfocus(focus) == unfocus(focus_smaller);



@*/
#endif
