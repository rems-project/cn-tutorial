/*@
function (datatype seq) flatten (datatype Dll L) {
    match L {
        Empty_Dll {} => { Seq_Nil {} }
        Dll {left: l, curr: n, right: r} => { 
            append(l, Seq_Cons {head: n.data, tail: r})
        }
    }
}
@*/