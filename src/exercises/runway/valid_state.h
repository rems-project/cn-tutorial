/*@
function (boolean) valid_state (struct State s) {
     (s.ModeA == INACTIVE() || s.ModeA == ACTIVE()) &&
     (s.ModeD == INACTIVE() || s.ModeD == ACTIVE()) &&
     (s.ModeA == INACTIVE() || s.ModeD == INACTIVE()) &&

     (s.W_A >= 0i32 && s.W_D >= 0i32) &&
     (0i32 <= s.Runway_Time && s.Runway_Time <= 5i32) && 
     (0i32 <= s.Plane_Counter && s.Plane_Counter <= 3i32) && 

     (s.ModeA == INACTIVE() && s.ModeD == INACTIVE() 
        implies s.Plane_Counter == 0i32) &&
     (s.Runway_Time > 0i32 
        implies (s.ModeA == ACTIVE() || s.ModeD == ACTIVE())) &&

     (s.Plane_Counter > 0i32 && s.ModeA == ACTIVE() implies s.W_D > 0i32) &&
     (s.Plane_Counter > 0i32 && s.ModeD == ACTIVE() implies s.W_A > 0i32)
}
@*/
