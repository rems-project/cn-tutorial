/*@
function (datatype Seq_Node) Dll_Rest (datatype Dll L) {
    match L {
        Empty_Dll {} => { Seq_Node_Nil {} }
        Dll {first: _, n: _, rest: r} => { r }
    }
}

function (datatype Seq_Node) Dll_First(datatype Dll L) {
    match L {
        Empty_Dll {} => { Seq_Node_Nil {} }
        Dll {first: f, n: _, rest: _} => { f }
    }
}

function (struct node) Dll_Node (datatype Dll L) {
    match L {
        Empty_Dll {} => {  default<struct node> }
        Dll {first: _, n: n, rest: _} => { n }
    }
}

function (struct node) Seq_Node_Head(datatype Seq_Node S) {
    match S {
        Seq_Node_Nil {} => {  default<struct node> }
        Seq_Node_Cons {n: n, tail: _} => { n }
    }
}

function (datatype seq) Seq_Node_Tail (datatype Seq_Node S) {
    match S {
        Seq_Node_Nil {} => {  Seq_Nil {} }
        Seq_Node_Cons {n: _, tail: t} => { t }
    }
}
@*/