
int inc_1_pre(int i) 
/*@ requires 
      let MAXi32 = 2147483647; 
      i + 1 <  MAXi32;
    ensures return == i + 1; @*/
{ 
  int start, pre, post; 
  start = i; 
  pre = ++i; 
  #ifdef CN_INSTRUMENT
  /*@ assert(pre == start+1); @*/
  #else
  assert(pre == start+1);
  #endif
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
  inc_1_pre(i);
  inc_1_post(i);
}