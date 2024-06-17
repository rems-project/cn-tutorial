struct State init()
/*@ requires true;
    ensures valid_state(return);
@*/
{
    struct State initial = {1,1,0,0,0};
    return initial;
}

struct State increment_W_A(struct State s) 
/*@ requires valid_state(s);
             (i64) s.W_A < 2147483647i64;
    ensures valid_state(return);
            return.W_B == s.W_B;
            return.Cross_Counter == s.Cross_Counter;
            return.W_A == s.W_A + 1i32;
            return.LightA == s.LightA;
            return.LightB == s.LightB;
@*/
{
  struct State temp = s;
  temp.W_A = s.W_A + 1;
  return temp;
}

struct State increment_W_B(struct State s) 
/*@ requires valid_state(s);
             (i64) s.W_B < 2147483647i64;
    ensures valid_state(return);
            return.W_A == s.W_A;
            return.Cross_Counter == s.Cross_Counter;
            return.W_B == s.W_B + 1i32;
            return.LightA == s.LightA;
            return.LightB == s.LightB;
@*/
{
  struct State temp = s;
  temp.W_B = s.W_B + 1;
  return temp;
}