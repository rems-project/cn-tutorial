struct State init()
/*@ requires true;
    ensures valid_state(return);
@*/
{
    struct State initial = {INACTIVE,INACTIVE,0,0,0,0};
    return initial;
}

struct State increment_Plane_Counter(struct State s)
/*@ requires valid_state(s);
             0i32 <= s.Plane_Counter;
             s.Plane_Counter <= 2i32;
             s.ModeA == ACTIVE() || s.ModeD == ACTIVE();
             s.ModeA == ACTIVE() implies s.W_D > 0i32;
             s.ModeD == ACTIVE() implies s.W_A > 0i32;
    ensures  valid_state(return);
             s.Plane_Counter == return.Plane_Counter - 1i32;
             s.Runway_Time == return.Runway_Time;
             s.ModeA == return.ModeA;
             s.ModeD == return.ModeD;
             s.W_A == return.W_A;
             s.W_D == return.W_D;
@*/
{
  struct State temp = s;
  temp.Plane_Counter = s.Plane_Counter + 1;
  return temp;
}

struct State reset_Plane_Counter(struct State s)
/*@ requires valid_state(s);
    ensures  valid_state(return);
             return.Plane_Counter == 0i32;
             s.Runway_Time == return.Runway_Time;
             s.ModeA == return.ModeA;
             s.ModeD == return.ModeD;
             s.W_A == return.W_A;
             s.W_D == return.W_D;
@*/
{
  struct State temp = s;
  temp.Plane_Counter = 0;
  return temp;
}