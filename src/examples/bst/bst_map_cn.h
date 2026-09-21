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

type_synonym RangedBST = { BST tree, Interval range }
type_synonym RangedNode = {
  struct MapNode node,
  BST smaller,
  BST larger,
  Interval range
}

function (boolean) validBST(struct MapNode node, Interval smaller, Interval larger) {
  (smaller.empty || smaller.upper < node.key) &&
  (larger.empty || node.key < larger.lower)
}


predicate RangedNode RangedNode(pointer root) {
   take node = Owned<struct MapNode>(root);
   take smaller = RangedBST(node.smaller);
   take larger  = RangedBST(node.larger);
   assert (validBST(node, smaller.range, larger.range));
   return { node: node, smaller: smaller.tree, larger: larger.tree,
            range: joinInterval(smaller.range, larger.range) };
}

// A binary search tree, and the interval for all its keys.
predicate RangedBST RangedBST(pointer root) {
  if (is_null(root)) {
    return { tree: Leaf {}, range: emptyInterval() };
  } else {
    take node = RangedNode(root);
    let data = getNodeData(node.node);
    return { tree: Node { data: data, smaller: node.smaller, larger: node.larger },
             range: node.range };
  }
}

// An arbitrary binary search tree.
predicate BST BST(pointer root) {
  take result = RangedBST(root);
  return result.tree;
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

predicate BSTFocus BSTFocus(pointer root, pointer child) {
  if (is_null(child)) {
    take tree = BST(root);
    return AtLeaf { tree: tree };
  } else {
    take node    = RangedNode(child);
    take result  = BSTNodeUpTo(root, child, node.node, node.range);
    return AtNode { done: result.tree, node: node.node,
                    smaller: node.smaller, larger: node.larger };
  }
}

// Consume parts of the tree starting at `p` until we get to `c`.
// We do not consume `c`.
// `child` is the node stored at `c`.
predicate RangedBST BSTNodeUpTo(pointer p, pointer c, struct MapNode child, Interval range) {
  if (ptr_eq(p,c)) {
    return { tree: Leaf {}, range: range };
  } else {
    take parent = Owned<struct MapNode>(p);
    take result = BSTNodeChildUpTo(c, child, range, parent);
    return result;
  }
}

// Starting at a parent with data `data` and children `smaller` and `larger`,
// we go toward `c`, guided by its value, `target`.
predicate RangedBST
  BSTNodeChildUpTo(pointer c, struct MapNode target, Interval range, struct MapNode parent) {
  if (parent.key < target.key) {
    take small = RangedBST(parent.smaller);
    take large = BSTNodeUpTo(parent.larger, c, target, range);
    assert(validBST(parent, small.range, large.range));
    return { tree: Node { data: getNodeData(parent), smaller: small.tree, larger: large.tree },
             range: joinInterval(small.range,large.range) };
  } else {
  if (parent.key > target.key) {
    take small = BSTNodeUpTo(parent.smaller, c, target, range);
    take large = RangedBST(parent.larger);
    assert(validBST(parent, small.range, large.range));
    return { tree: Node { data: getNodeData(parent), smaller: small.tree, larger: large.tree },
             range: joinInterval(small.range,large.range) };
  } else {
    // We should never get here, but asserting `false` is not allowed
    return default<RangedBST>;
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

function (BST) focusDone(BSTFocus focus) {
  match focus {
    AtLeaf { tree: tree } => { tree }
    AtNode { done: tree, node: _, smaller: _, larger: _ } => { tree }
  }
}



lemma FocusedGo(pointer root, pointer cur, boolean smaller)
  requires
    !is_null(cur);
    take focus = BSTFocus(root,cur);
  ensures
    let node = fromBSTFocusNode(focus).node;
    take new_focus = BSTFocus(root, if (smaller) { node.smaller } else { node.larger });
    unfocus(focus) == unfocus(new_focus);


// It's quite unfortunate that we have to copy the lemma here.
lemma FocusedGoKey(pointer root, pointer cur, boolean smaller, KEY key)
  requires
    !is_null(cur);
    take focus = BSTFocus(root,cur);
  ensures
    let node = fromBSTFocusNode(focus).node;
    take new_focus = BSTFocus(root, if (smaller) { node.smaller } else { node.larger });
    unfocus(focus) == unfocus(new_focus);

    if (!member(key, focusDone(focus)) && node.key != key) {
      !member(key, focusDone(new_focus))
    } else {
      true
    };



@*/
#endif
