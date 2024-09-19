#include "binary_tree.h"

// Here's a definition.
/*@
    predicate (datatype binary_tree) IntBst(pointer p) {
        if (is_null(p)) {
            return Tree_Leaf {};
        } else {
            take n = Owned<struct int_tree>(p);

            take l = IntBst(n.left);
            assert (match l {
                Tree_Leaf {} => { true }
                Tree_Node {
                    key: k,
                    left: _,
                    right: _
                } => { k < n.key }
            });

            take r = IntBst(n.right);
            assert (match r {
                Tree_Leaf {} => { true }
                Tree_Node {
                    key: k,
                    left: _,
                    right: _
                } => { n.key < k }
            });
            return Tree_Node { key: n.key, left: l, right: r };
        }
    }
@*/
// And here's one that reuses our `IntTree` predicate.
/*@
    function [rec] (boolean) isSortedTree(datatype binary_tree tree) {
        match tree {
            Tree_Leaf {} => { true }
            Tree_Node {
                key: k,
                left: l,
                right: r
            } => {
                (match l {
                    Tree_Leaf {} => { true }
                    Tree_Node {
                        key: k_l,
                        left: _,
                        right: _
                    } => {
                        k_l < k && isSortedTree(l)
                    }
                }) &&
                (match r {
                    Tree_Leaf {} => { true }
                    Tree_Node {
                        key: k_r,
                        left: _,
                        right: _
                    } => {
                        k < k_r && isSortedTree(r)
                    }
                })
            }
        }
    }

    predicate (datatype binary_tree) IntBstAlt(pointer p) {
        take T = IntTree(p);
        assert(isSortedTree(T));
        return T;
    }
@*/

/*@
    function [rec] (datatype binary_tree) insert(datatype binary_tree tree, i32 to_insert) {
        match tree {
            Tree_Leaf {} => {
                Tree_Node {
                    key: to_insert,
                    left: Tree_Leaf {},
                    right: Tree_Leaf {}
                }
            }
            Tree_Node {
                key: k,
                left: l,
                right: r
            } => {
                if (to_insert < k) {
                    Tree_Node {
                        key: k,
                        left: insert(l, to_insert),
                        right: r
                    }
                } else {
                    if (k < to_insert) {
                        Tree_Node {
                            key: k,
                            left: l,
                            right: insert(r, to_insert)
                        }
                    } else {
                        tree
                    }
                }
            }
        }
    }
@*/

struct int_tree* insert(struct int_tree* tree, int key)
    /*@
    requires
        take T1 = IntBst(tree);
    ensures
        take T2 = IntBst(return);
        T2 == insert(T1, key);
    @*/
{
    if (tree == 0) {
        struct int_tree* ret = mallocIntTree();
        ret->key = key;
        ret->left = 0;
        ret->right = 0;

        /*@ unfold insert(T1, key); @*/
        return ret;
    }

    if (key < tree->key) {
        tree->left = insert(tree->left, key);
    }
    else if (tree->key < key) {
        tree->right = insert(tree->right, key);
    }
    return tree;
}

/*@
    lemma BstIsTree(pointer p)
    requires
        take T = IntBst(p);
    ensures
        take T2 = IntTree(p);
@*/

int main() {
    struct int_tree* tree = emptyTree();
    // If we used `IntBstAlt` we would need to somehow unfold
    // `isSortedTree`, so that CN knows that `IntBstAlt(tree)`.
    /*@ split_case is_null(tree); @*/
    tree = insert(tree, 5);
    tree = insert(tree, 10);
    tree = insert(tree, 0);
    tree = insert(tree, 7);
    tree = insert(tree, 3);
    /*@ apply BstIsTree(tree); @*/
    deepFreeIntTree(tree);

    return 0;
}
