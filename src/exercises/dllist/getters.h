/*@
function (datatype List) Right_Sublist (datatype DlList L) {
    match L {
        Empty_DlList {} => { Nil{} }
        Nonempty_DlList {left: _, curr: _, right: r} => { r }
    }
}

function (datatype List) Left_Sublist (datatype DlList L) {
    match L {
        Empty_DlList {} => { Nil {} }
        Nonempty_DlList {left: l, curr: _, right: _} => { l }
    }
}

function (struct dllist) Node (datatype DlList L) {
    match L {
        Empty_DlList {} => {  default<struct dllist> }
        Nonempty_DlList {left: _, curr: n, right: _} => { n }
    }
}
@*/
