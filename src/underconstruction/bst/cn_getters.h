// Defines basic CN functions to extract a member of the Tree datatype

/*@
function (i32) Data_Of (datatype Tree sapling) 
{
  match sapling 
  {
    Leaf {} => 
    {
      default<i32>
    }
    Node {Left : _, Data : dat, Right: _} => 
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
    Node {Left : left, Data : _ , Right: _} => 
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
    Node {Left : _, Data : _ , Right: right} => 
    {
      right
    }
  }
}
@*/
