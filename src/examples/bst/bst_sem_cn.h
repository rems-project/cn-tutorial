#ifndef BST_SEM_CN_H
#define BST_SEM_CN_H

// Functional Sepcification of Binary Search Tree

/*@
type_synonym KEY = i32
type_synonym VALUE = i64
type_synonym NodeData = { KEY key, VALUE value }

function (KEY) minKey() { MINi32() }
function (KEY) maxKey() { MAXi32() }
function (KEY) incKey(KEY x) { if (x < maxKey()) { x + 1i32 } else { x } }
function (KEY) decKey(KEY x) { if (x > minKey()) { x - 1i32 } else { x } }

type_synonym Interval = { KEY lower, KEY upper }
function (Interval) anyKey() {{ lower: minKey(), upper: maxKey() }}

type_synonym Intervals = { Interval lower, Interval upper }
function (Intervals) splitInterval(KEY x, Interval i) {
  { lower: { lower: i.lower, upper: decKey(x) },
    upper: { lower: incKey(x), upper: i.upper }
  }
}

function (boolean) inInterval(KEY x, Interval i) {
  i.lower <= x && x <= i.upper
}


// A binary dearch tree
datatype BST {
  Leaf {},
  Node { NodeData data, BST smaller, BST larger }
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