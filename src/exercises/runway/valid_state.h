/*@
function (boolean) valid_state (struct State s) {
     (s.ModeA == INACTIVE() || s.ModeA == ACTIVE()) &&
     (s.ModeD == INACTIVE() || s.ModeD == ACTIVE()) &&
     (s.ModeA == INACTIVE() || s.ModeD == INACTIVE()) &&

     (s.W_A >= 0 && s.W_D >= 0) &&
     (0 <= s.Runway_Time && s.Runway_Time <= 5) && 
     (0 <= s.Plane_Counter && s.Plane_Counter <= 3) && 

     (s.ModeA == INACTIVE() && s.ModeD == INACTIVE() 
        implies s.Plane_Counter == 0) &&
     (s.Runway_Time > 0 
        implies (s.ModeA == ACTIVE() || s.ModeD == ACTIVE())) &&

     (s.Plane_Counter > 0 && s.ModeA == ACTIVE() implies s.W_D > 0) &&
     (s.Plane_Counter > 0 && s.ModeD == ACTIVE() implies s.W_A > 0)
}
@*/
