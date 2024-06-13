struct State {
  struct Traffic_Light LightA;
  struct Traffic_Light LightB;
  int W_A;
  int W_B;
  int Cross_Counter;
};

/*@
function (bool) valid_state (struct State s) {
     (valid_light(s.LightA)) &&
     (valid_light(s.LightB)) &&
     (s.LightA.Red == 1i32 || s.LightB.Red == 1i32) &&
     (s.W_A >= 0i32 && s.W_B >= 0i32) &&
     (0i32 <= s.Cross_Counter && s.Cross_Counter <= 5i32) &&
     (s.LightA.Red != 1i32 || s.LightB.Red != 1i32 || s.Cross_Counter == 0i32)
}
@*/
