// Allocate an int in memory and assign to it 

// malloc() is not defined by default in CN. We can define a fake malloc()
// function that only works on ints.

int *my_malloc__int()
/*@ trusted;
    ensures take New = W<int>(return); @*/
{}

int *malloc__1()
/*@ ensures 
      take New = RW<int>(return);
      New == 7i32;
      *return == 7i32; @*/  // <-- Alternative syntax 
{
  int *new;
  new = my_malloc__int();
  *new = 7; // Have to initialize the memory before it's RW
  return new;
}
