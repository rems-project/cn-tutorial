// Pre and post-read decrement 

int dec_1_pre(int i) 
/*@ requires i >= 1;
    ensures return == i - 1; @*/
{ 
  int start, pre, post; 
  start = i; 
  pre = --i; 
  #ifdef CN_INSTRUMENT
  /*@ assert(pre == start-1); @*/
  #else
  assert(pre == start-1);
  #endif
  return i; 
}

int dec_1_post(int i) 
/*@ requires i >= 1;
    ensures return == i - 1; @*/
{ 
  int start, pre, post; 
  start = i; 
  pre = i--; 
  #ifdef CN_INSTRUMENT
  /*@ assert(pre == start); @*/
  #else
  assert(pre == start);
  #endif
  return i;
}

int main(void)
/*@ trusted; @*/
{
  int i = 42;
  dec_1_pre(i);
  dec_1_post(i);
}