// Pre and post-read decrement 

int dec_1_pre(int i) 
/*@ requires i >= 1i32; @*/
/*@ ensures return == i - 1i32; @*/
{ 
  int start, pre, post; 
  start = i; 
  pre = --i; 
  assert(pre == start-1);
  return i; 
}

int dec_1_post(int i) 
/*@ requires i >= 1i32; @*/
/*@ ensures return == i - 1i32; @*/
{ 
  int start, pre, post; 
  start = i; 
  pre = i--; 
  assert(pre == start);
  return i; 
}