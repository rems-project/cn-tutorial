// Defines basic CN functions to extract a member of the Tree datatype

/*@
function (i32) get_data (datatype Tree sapling) 
{
  match sapling 
  {
    Leaf {} => 
    {
      default<i32>
    }
    Node {left : _, data : dat, right: _} => 
    {
      dat
    }
  }
}

function (datatype Tree) get_lb (datatype Tree sapling) 
{
  match sapling 
  {
    Leaf {} => 
    {
      Leaf {}
    }
    Node {left : left, data : _ , right: _} => 
    {
      left
    }
  }
}

function (datatype Tree) get_rb (datatype Tree sapling) 
{
  match sapling 
  {
    Leaf {} => 
    {
      Leaf {}
    }
    Node {left : _, data : _ , right: right} => 
    {
      right
    }
  }
}
@*/
