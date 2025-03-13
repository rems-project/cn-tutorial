// FILL IN: This is where we define the Tree datatype and the
// associated Tree_At predicate

/*@
datatype Tree {
    Leaf {},
    Node {datatype Tree Left, i32 Data, datatype Tree Right}
} 

predicate (datatype Tree) Tree_At (pointer t) 
{
    if (is_null(t))
    {
        return Leaf{};
    }
    else
    {
        take T = RW<struct node>(t);
        take L = Tree_At(T.left);
        assert (L == Leaf{} || Data_Of(L) < T.data);
        take R = Tree_At(T.right);
        assert (R == Leaf{} || Data_Of(R) >= T.data);
        return (Node {Left: L, Data: T.data, Right: R});
    }
}
@*/
