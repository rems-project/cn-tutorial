#ifndef BST_SEM_CN_H
#define BST_SEM_CN_H

// Functional Sepcification of Binary Search Tree

/*@
type_synonym KEY = i32
type_synonym VALUE = i64
type_synonym NodeData = { KEY key, VALUE value }

type_synonym Interval = { KEY lower, KEY upper, boolean empty }

function (Interval) emptyInterval() {
  { lower: default<KEY>, upper: default<KEY>, empty: true }
}



function (Interval) joinInterval(Interval smaller, Interval larger) {
  if (smaller.empty) {
    larger
  } else {
  if (larger.empty) {
    smaller
  } else {
    { lower: smaller.lower, upper: larger.upper, empty: false }
  }}
}

// A binary dearch tree
datatype BST {
  Leaf {},
  Node { NodeData data, BST smaller, BST larger }
}

// A selector for the case when we know that the tree is a `Node`.
function ({ NodeData data, BST smaller, BST larger }) fromBSTNode(BST node) {
  match node {
    Leaf {} => { default<{ NodeData data, BST smaller, BST larger }> }
    Node { data: data, smaller: smaller, larger: larger } => {
      { data: data, smaller: smaller, larger: larger }
    }
  }
}

datatype VALUEOption {
  VALUENone {},
  VALUESome { VALUE value }
}

function [rec] (VALUEOption) lookup(KEY key, BST tree) {
  match tree {
    Leaf {} => { VALUENone {} }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (data.key == key) {
        VALUESome { value: data.value }
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

function [rec] (boolean) member(KEY k, BST tree) {
  match tree {
    Leaf {} => { false }
    Node { data: data, smaller: smaller, larger: larger } => {
      data.key == k ||
      k < data.key && member(k,smaller) ||
      k > data.key && member(k,larger)
    }
  }
}



function [rec] (BST) setKey(KEY k, BST root, BST value) {
  match root {
    Leaf {} => { value }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (k < data.key) {
        Node { data: data, smaller: setKey(k, smaller, value), larger: larger }
      } else {
        Node { data: data, smaller: smaller, larger: setKey(k, larger, value) }
      }
    }
  }
}


@*/

#endif