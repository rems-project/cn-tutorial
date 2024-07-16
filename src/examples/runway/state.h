#define INACTIVE 0
    /*@ function (i32) INACTIVE () @*/
    static int c_INACTIVE() /*@ cn_function INACTIVE; @*/ { return INACTIVE; }

#define ACTIVE 1
    /*@ function (i32) ACTIVE () @*/
    static int c_ACTIVE() /*@ cn_function ACTIVE; @*/ { return ACTIVE; }

struct State {
  int ModeA;
  int ModeD;

  int W_A;
  int W_D;

  int Runway_Time;
  int Plane_Counter;
};