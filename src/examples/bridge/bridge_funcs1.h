struct State init()
/*@ requires true;
    ensures valid_state(return);
@*/
{
    // LightA is initialized to red
    struct Traffic_Light la = {1,0};
    // LightB is initialized to red
    struct Traffic_Light lb = {1,0};

    struct State initial;
    initial.LightA = la;
    initial.LightB = lb;
    initial.W_A = 0;
    initial.W_B = 0;
    initial.Cross_Counter = 0;

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