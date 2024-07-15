/*@
function (datatype seq) flatten (datatype Dll L) {
    match L {
        Empty_Dll {} => { Seq_Nil {} }
        Dll {first: f, n: n, rest: r} => { 
            match f {
                Seq_Node_Nil {} => {
                    match r {
                        Seq_Node_Nil {} => { 
                            Seq_Cons {head: n.data, tail: Seq_Nil {}} 
                        }
                        Seq_Node_Cons {n: nextNode, tail: t} => {  
                            Seq_Cons {head: n.data, tail: Seq_Cons{ head: nextNode.data, tail: t}}
                        }
                    }
                }
                Seq_Node_Cons {n: prevNode, tail: t} => { 
                    match r {
                        Seq_Node_Nil {} => { 
                            rev(Seq_Cons {head: n.data, tail: Seq_Cons {head: prevNode.data, tail: t}})
                        }
                        Seq_Node_Cons {n: nextNode, tail: t2} => {  
                            append(rev(Seq_Cons {head: prevNode.data, tail: t2}), Seq_Cons {head: n.data, tail: Seq_Cons{ head: nextNode.data, tail: t2}})
                        }
                    }
                }
            }
        }
    }
}

function (datatype seq) Seq_Node_to_Seq(datatype Seq_Node L) {
    match L {
        Seq_Node_Nil {} => { Seq_Nil {} }
        Seq_Node_Cons {n: n, tail: t} => { Seq_Cons {head: n.data, tail: t } }
    }
}
@*/