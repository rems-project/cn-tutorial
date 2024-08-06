// Defines the CN datatype for the Binary Tree Nodes
// Also, defines CN predicates for ownership of the tree nodes

/*@

datatype tree {
    Tree_Nil {},
    Tree_Cons {datatype tree left, i32 data, datatype tree right}
} 

predicate (datatype tree) IntTree(pointer p) 
{
    if (is_null(p))
    {
        return Tree_Nil{};
    }
    else
    {
        take T = Owned<struct TreeNode>(p);
        take left_b = IntTree(T.left);
        assert (left_b == Tree_Nil{} || get_data(left_b) < T.data);
        take right_b = IntTree(T.right);
        assert (right_b == Tree_Nil{} || get_data(right_b) >= T.data);
        return (Tree_Cons {left: left_b, data: T.data, right: right_b});
    }
}

@*/