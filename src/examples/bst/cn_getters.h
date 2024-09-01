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
    Node {Left : _, data : dat, right: _} => 
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
    Node {Left : left, data : _ , right: _} => 
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
    Node {Left : _, data : _ , right: right} => 
    {
      right
    }
  }
}
@*/
