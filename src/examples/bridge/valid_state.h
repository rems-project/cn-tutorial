/*@
function (bool) valid_state (struct State s) {
     (s.LightA == 1i32 || s.LightA == 2i32) &&
     (s.LightB == 1i32 || s.LightB == 2i32) &&
     (s.LightA == 1i32 || s.LightB == 1i32) &&
     (s.W_A >= 0i32 && s.W_B >= 0i32) &&
     (0i32 <= s.Cross_Counter && s.Cross_Counter <= 5i32) &&
     (s.LightA != 1i32 || s.LightB != 1i32 || s.Cross_Counter == 0i32)
}
@*/
