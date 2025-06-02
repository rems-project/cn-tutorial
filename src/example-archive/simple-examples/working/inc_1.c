
int inc_1_pre(int i) 
/*@ requires 
      let MAXi32 = 2147483647i64; 
      (i64) i + 1i64 <  MAXi32;
    ensures return == i + 1i32; @*/
{ 
  int start, pre, post; 
  start = i; 
  pre = ++i; 
  assert(pre == start+1);
  return i; 
}

int inc_1_post(int i) 
/*@ requires 
      let MAXi32 = 2147483647i64; 
      (i64) i + 1i64 <  MAXi32;
    ensures return == i + 1i32; @*/
{ 
  int start, pre, post; 
  start = i; 
  pre = i++; 
  assert(pre == start);
  return i; 
}
