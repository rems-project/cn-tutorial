/*@
function (bool) valid_state (struct State s) {
     (s.LightA == RED() || s.LightA == GREEN()) &&
     (s.LightB == RED() || s.LightB == GREEN()) &&
     (s.LightA == RED() || s.LightB == RED()) &&
     (s.W_A >= 0i32 && s.W_B >= 0i32) &&
     (0i32 <= s.Cross_Counter && s.Cross_Counter <= 5i32) &&
     ((s.LightA != RED() || s.LightB != RED()) || (s.Cross_Counter == 0i32))
}
@*/
