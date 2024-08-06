#ifndef TREE_H
#define TREE_H

struct int_tree {
    int key;
    struct int_tree* left;
    struct int_tree* right;
};

/*@
    datatype binary_tree {
        Tree_Leaf {},
        Tree_Node { i32 key, datatype binary_tree left, datatype binary_tree right }
    }

    predicate (datatype binary_tree) IntTree(pointer p) {
        if (is_null(p)) {
            return Tree_Leaf {};
        } else {
            take n = Owned<struct int_tree>(p);
            take l = IntTree(n.left);
            take r = IntTree(n.right);
            return Tree_Node { key: n.key, left: l, right: r };
        }
    }
@*/

extern struct int_tree* mallocIntTree();
/*@ spec mallocIntTree();
    requires
        true;
    ensures
        take T = Block<struct int_tree>(return);
        !is_null(return);
@*/

extern void freeIntTree(struct int_tree* p);
/*@ spec freeIntTree(pointer p);
    requires
        take T = Block<struct int_tree>(p);
    ensures
        true;
@*/

void deepFreeIntTree(struct int_tree* p)
/*@
    requires
        take T = IntTree(p);
@*/
{
    if (p == 0) {
        return;
    }

    deepFreeIntTree(p->left);
    deepFreeIntTree(p->right);
    freeIntTree(p);
}

struct int_tree* emptyTree()
    /*@
    ensures
        take T = IntTree(return);
        T == Tree_Leaf {};
    @*/
{
    return 0;
}

struct int_tree* newNode(int key)
    /*@
        ensures
            take T = IntTree(return);
            T == Tree_Node {
                key: key,
                left: Tree_Leaf {},
                right: Tree_Leaf {}
            };
    @*/
{
    struct int_tree* p = mallocIntTree();
    p->key = key;
    p->left = 0;
    p->right = 0;
    return p;
}

struct int_tree* deepCopyRecursive(struct int_tree* p)
    /*@
        requires
            take T = IntTree(p);
        ensures
            take T_ = IntTree(p);
            T == T_;
            take T2 = IntTree(return);
            T == T2;
    @*/
{
    if (p == 0) {
        return 0;
    }

    struct int_tree* q = mallocIntTree();
    q->key = p->key;
    q->left = deepCopyRecursive(p->left);
    q->right = deepCopyRecursive(p->right);
    return q;
}

#endif
