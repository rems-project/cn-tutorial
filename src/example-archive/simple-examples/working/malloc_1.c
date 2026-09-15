// Allocate an int in memory and assign to it 

// malloc() is not defined by default in CN. We can define a fake malloc()
// function that only works on ints.

#ifdef CN_INSTRUMENT
void* cn_malloc(unsigned long size);
#endif 

int *my_malloc__int()
/*@ trusted;
    ensures take New = W<int>(return); @*/
{
  #ifdef CN_INSTRUMENT
  int *p = cn_malloc(sizeof(int));
  return p;
  #endif
}

int *malloc__1()
/*@ ensures 
      take New = RW<int>(return);
      New == 7;
      *return == 7; @*/  // <-- Alternative syntax 
{
  int *new;
  new = my_malloc__int();
  *new = 7; // Have to initialize the memory before it's RW
  return new;
}

int main(void)
/*@ trusted; @*/
{
  my_malloc__int();
}

