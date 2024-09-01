/*@
function (datatype List) Right (datatype Nonempty_Dll L) {
    match L {
        Empty_Dll {} => { Nil{} }
        Nonempty_Dll {left: _, curr: _, right: r} => { r }
    }
}

function (datatype List) Left (datatype Nonempty_Dll L) {
    match L {
        Empty_Dll {} => { Nil {} }
        Nonempty_Dll {left: l, curr: _, right: _} => { l }
    }
}

function (struct dllist) Node (datatype Nonempty_Dll L) {
    match L {
        Empty_Dll {} => {  default<struct dllist> }
        Nonempty_Dll {left: _, curr: n, right: _} => { n }
    }
}
@*/