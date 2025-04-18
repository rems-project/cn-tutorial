#define INACTIVE 0
/*@ function (i32) INACTIVE() { 0i32 } @*/
static int c_INACTIVE()
/*@ requires true; 
    ensures return == INACTIVE(); @*/
{ return INACTIVE; }

#define ACTIVE 1
/*@ function (i32) ACTIVE() { 1i32 } @*/
static int c_ACTIVE()
/*@ requires true; 
    ensures return == ACTIVE(); @*/
{ return ACTIVE; }

struct State {
  int ModeA;
  int ModeD;

  int W_A;
  int W_D;

  int Runway_Time;
  int Plane_Counter;
};
