// Defines the CN datatype for the Binary Tree Nodes
// plus associated CN predicates

/*@
datatype Tree {
    Leaf {},
    Node {datatype Tree Left, i32 Data, datatype Tree Right}
} 

predicate (datatype Tree) Tree_At (pointer p) 
{
    if (is_null(p))
    {
        return Leaf{};
    }
    else
    {
        take T = Owned<struct node>(p);
        take left_b = Tree_At(T.left);
        assert (left_b == Leaf{} || get_data(left_b) < T.data);
        take right_b = Tree_At(T.right);
        assert (right_b == Leaf{} || get_data(right_b) >= T.data);
        return (Node {Left: left_b, Data: T.data, Right: right_b});
    }
}

@*/
