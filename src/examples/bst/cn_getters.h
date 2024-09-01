// Defines basic CN functions to extract a member of the tree datatype

/*@
function (i32) get_data (datatype tree sapling) 
{
  match sapling 
  {
    Tree_Nil {} => 
    {
      default<i32>
    }
    Tree_Cons {left : _, data : dat, right: _} => 
    {
      dat
    }
  }
}

function (datatype tree) get_lb (datatype tree sapling) 
{
  match sapling 
  {
    Tree_Nil {} => 
    {
      Tree_Nil {}
    }
    Tree_Cons {left : left, data : _ , right: _} => 
    {
      left
    }
  }
}

function (datatype tree) get_rb (datatype tree sapling) 
{
  match sapling 
  {
    Tree_Nil {} => 
    {
      Tree_Nil {}
    }
    Tree_Cons {left : _, data : _ , right: right} => 
    {
      right
    }
  }
}
@*/
