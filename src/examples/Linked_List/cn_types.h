/*@
datatype Dll {
    Empty_Dll {},
    Dll {datatype Seq_Node first, struct node n, datatype Seq_Node rest}
}

datatype Seq_Node {
    Seq_Node_Nil {},
    Seq_Node_Cons {struct node n, datatype seq tail}
}
@*/