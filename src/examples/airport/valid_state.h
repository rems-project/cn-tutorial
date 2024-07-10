/*@
function (bool) valid_state (struct State s) {
     (s.ModeA == INACTIVE() || s.ModeA == ACTIVE()) &&
     (s.ModeD == INACTIVE() || s.ModeD == ACTIVE()) &&
     (s.ModeA == INACTIVE() || s.ModeD == INACTIVE()) &&
     (s.W_A >= 0i32 && s.W_D >= 0i32) &&
     (0i32 <= s.Runway_Time && s.Runway_Time <= 5i32) && 
     (0i32 <= s.Plane_Counter && s.Plane_Counter <= 3i32) && 
     (s.ModeA == INACTIVE() && s.ModeD == INACTIVE() implies s.Plane_Counter == 0i32)
}
@*/


// /*@ assert(temp.ModeA == INACTIVE() || temp.ModeA == ACTIVE()); @*/
//   /*@ assert(temp.ModeD == INACTIVE() || temp.ModeD == ACTIVE()); @*/
//   /*@ assert(temp.ModeA == INACTIVE() || temp.ModeD == INACTIVE()); @*/
//   /*@ assert(temp.W_A >= 0i32 && temp.W_D >= 0i32); @*/
//   /*@ assert(0i32 <= temp.Runway_Time && temp.Runway_Time <= 5i32); @*/
//   /*@ assert(0i32 <= temp.Plane_Counter && temp.Plane_Counter <= 3i32); @*/ 
//   /*@ assert(s.Plane_Counter == 0i32 implies s.ModeA == INACTIVE() && s.ModeD == INACTIVE()); @*/