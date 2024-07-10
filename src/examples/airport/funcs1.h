// #include "state.h"
// #include "valid_state.h"

struct State init()
/*@ requires true;
    ensures valid_state(return);
@*/
{
    struct State initial = {INACTIVE,INACTIVE,0,0,0,0};
    return initial;
}

struct State increment_W_A(struct State s) 
/*@ requires valid_state(s);
             (i64) s.W_A < 2147483647i64;
    ensures valid_state(return);
            return.W_A == s.W_A + 1i32;
            return.W_D == s.W_D;
            
            return.ModeA == s.ModeA;
            return.ModeD == s.ModeD;

            return.Plane_Counter == s.Plane_Counter;
            return.Runway_Time == s.Runway_Time;
@*/
{
  struct State temp = s;
  temp.W_A = s.W_A + 1;
  return temp;
}

struct State increment_W_D(struct State s) 
/*@ requires valid_state(s);
             (i64) s.W_D < 2147483647i64;
    ensures valid_state(return);
            return.W_D == s.W_D + 1i32;
            return.W_A == s.W_A;
            
            return.ModeA == s.ModeA;
            return.ModeD == s.ModeD;

            return.Plane_Counter == s.Plane_Counter;
            return.Runway_Time == s.Runway_Time;
@*/
{
  struct State temp = s;
  temp.W_D = s.W_D + 1;
  return temp;
}
