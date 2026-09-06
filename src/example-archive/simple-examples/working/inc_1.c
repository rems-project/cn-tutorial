
int inc_1_pre(int i) 
/*@ requires 
      let MAXi32 = 2147483647; 
      i + 1 <  MAXi32;
    ensures return == i + 1; @*/
{ 
  int start, pre, post; 
  start = i; 
  pre = ++i; 
  assert(pre == start+1);
  return i; 
}

int inc_1_post(int i) 
/*@ requires 
      let MAXi32 = 2147483647; 
      i + 1 <  MAXi32;
    ensures return == i + 1; @*/
{ 
  int start, pre, post; 
  start = i; 
  pre = i++; 
  assert(pre == start);
  return i; 
}
