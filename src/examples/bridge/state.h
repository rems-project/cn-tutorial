#define RED 1
    /*@ function (i32) RED () @*/
    static int c_RED() /*@ cn_function RED; @*/ { return RED; }

#define GREEN 2
    /*@ function (i32) GREEN () @*/
    static int c_GREEN() /*@ cn_function GREEN; @*/ { return GREEN; }

struct State {
  int LightA;
  int LightB;

  int W_A;
  int W_B;

  int Cross_Counter;
};