/*@
function (datatype seq) Right (datatype Dll L) {
    match L {
        Empty_Dll {} => { Seq_Nil{} }
        Dll {left: _, n: _, right: r} => { r }
    }
}

function (datatype seq) Left (datatype Dll L) {
    match L {
        Empty_Dll {} => { Seq_Nil {} }
        Dll {left: l, n: _, right: _} => { l }
    }
}

function (struct node) Node (datatype Dll L) {
    match L {
        Empty_Dll {} => {  default<struct node> }
        Dll {left: _, n: n, right: _} => { n }
    }
}
@*/