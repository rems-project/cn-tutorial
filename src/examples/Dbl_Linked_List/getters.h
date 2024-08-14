/*@
function (datatype List) Right (datatype Dll L) {
    match L {
        Empty_Dll {} => { Nil{} }
        Dll {left: _, curr: _, right: r} => { r }
    }
}

function (datatype List) Left (datatype Dll L) {
    match L {
        Empty_Dll {} => { Nil {} }
        Dll {left: l, curr: _, right: _} => { l }
    }
}

function (struct node) Node (datatype Dll L) {
    match L {
        Empty_Dll {} => {  default<struct node> }
        Dll {left: _, curr: n, right: _} => { n }
    }
}
@*/