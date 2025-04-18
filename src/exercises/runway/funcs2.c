#include "state.h"
#include "valid_state.h"
#include "funcs1.h"

struct State increment_Runway_Time(struct State s)
/* --BEGIN-- */
/*@ requires valid_state(s);
             0i32 <= s.Runway_Time;
             s.Runway_Time <= 4i32;
             s.ModeA == ACTIVE() || s.ModeD == ACTIVE();
    ensures  valid_state(return);
             s.Plane_Counter == return.Plane_Counter;
             s.ModeA == return.ModeA;
             s.ModeD == return.ModeD;
@*/
/* --END-- */
{
  struct State temp = s;
  temp.Runway_Time = s.Runway_Time + 1;
  return temp;
}

struct State reset_Runway_Time(struct State s)
/* --BEGIN-- */
/*@ requires valid_state(s);
    ensures  valid_state(return);
             return.Runway_Time == 0i32;
             s.ModeA == return.ModeA;
             s.ModeD == return.ModeD;
             s.W_A == return.W_A;
             s.W_D == return.W_D;
             s.Plane_Counter == return.Plane_Counter;
@*/
/* --END-- */
{
  struct State temp = s;
  temp.Runway_Time = 0;
  return temp;
}

struct State arrive(struct State s)
/* --BEGIN-- */
/*@ requires valid_state(s);
             s.ModeA == ACTIVE() && s.W_A >= 1i32;
             s.Plane_Counter <= 2i32;
    ensures  valid_state(return);
             s.Runway_Time == return.Runway_Time;
             s.ModeA == return.ModeA;
             s.ModeD == return.ModeD;
             s.W_D == return.W_D;
             s.W_D == 0i32 
               implies s.Plane_Counter == return.Plane_Counter;
             s.W_D > 0i32 
               implies s.Plane_Counter == return.Plane_Counter - 1i32;
@*/
/* --END-- */
{
  struct State temp = s;
  temp.W_A = s.W_A - 1;
  if (s.W_D > 0) {
    temp = increment_Plane_Counter(temp);
  }
  return temp;
}

struct State depart(struct State s)
/* --BEGIN-- */
/*@ requires valid_state(s);
             s.ModeD == ACTIVE() && s.W_D >=1i32;
             s.Plane_Counter <= 2i32;
    ensures  valid_state(return);
              s.Runway_Time == return.Runway_Time;
              s.ModeA == return.ModeA;
              s.ModeD == return.ModeD;
              s.W_A == return.W_A;
@*/
/* --END-- */
{
  struct State temp = s;
  temp.W_D = s.W_D - 1;
  if (s.W_A > 0) {
    temp = increment_Plane_Counter(temp);
  }
  return temp;
}

struct State switch_modes(struct State s) 
/* --BEGIN-- */
/*@ requires valid_state(s);
             s.ModeA == ACTIVE() || s.ModeD == ACTIVE();
             s.Plane_Counter == 0i32;
    ensures  valid_state(return);
             return.ModeA == ACTIVE() || return.ModeD == ACTIVE();
             return.ModeA == s.ModeD;
             return.ModeD == s.ModeA;
             return.W_A == s.W_A;
             return.W_D == s.W_D;
             return.Runway_Time == s.Runway_Time;
             s.Plane_Counter == return.Plane_Counter;
@*/
/* --END-- */
{
  struct State temp = s;
  if (s.ModeA == INACTIVE) {
    // if arrival mode is inactive, make it active
    temp.ModeA = ACTIVE;
  } else {
    // if arrival mode is active, make it inactive
    temp.ModeA = INACTIVE;
  }
  if (s.ModeD == INACTIVE) {
    // if departure mode is inactive, make it active
    temp.ModeD = ACTIVE;
  } else {
    // if departure mode is active, make it inactive
    temp.ModeD = INACTIVE;
  }
  return temp;
}

// This function represents what happens every minute at the airport. 
// One `tick` corresponds to one minute.
struct State tick(struct State s)
/* --BEGIN-- */
/*@ requires valid_state(s);
             (i64) s.Plane_Counter < 2147483647i64;
             (i64) s.W_A < 2147483647i64;
             (i64) s.W_D < 2147483647i64;
    ensures valid_state(return);
            (s.W_A > 0i32 && s.W_D == 0i32 && s.Runway_Time == 0i32 
               implies return.ModeA == ACTIVE());
            (s.W_D > 0i32 && s.W_A == 0i32 && s.Runway_Time == 0i32 
               implies return.ModeD == ACTIVE());
@*/
/* --END-- */
{
    // Plane on the runway
    if (s.Runway_Time > 0)
    {
      if (s.Runway_Time == 5)
      {
        s = reset_Runway_Time(s);
      } else {
        s = increment_Runway_Time(s);
      }
      return s;
    }
    // Plane chosen to arrive
    else if (s.ModeA == ACTIVE && s.W_A > 0 && s.Plane_Counter < 3) {
      s = arrive(s);
      s = increment_Runway_Time(s);
      return s;
    } 
    // Plane chosen to depart
    else if (s.ModeD == ACTIVE && s.W_D > 0 && s.Plane_Counter < 3) {
      s = depart(s);
      s = increment_Runway_Time(s);
      return s;
    }
    // Need to switch modes
    else {
      // Need to switch from arrival to departure mode
      if (s.ModeA == ACTIVE) {
        s = reset_Plane_Counter(s);
        s = switch_modes(s);
        // If there are planes waiting to depart, let one depart
        if (s.W_D > 0) {
          s = depart(s);
          s = increment_Runway_Time(s);
        }
        return s;
      }
      // Need to switch from departure to arrival mode
      else if (s.ModeD == ACTIVE) {
        s = reset_Plane_Counter(s);
        s = switch_modes(s);

        // If there are planes waiting to arrive, let one arrive
        if (s.W_A > 0) {
          s = arrive(s);
          s = increment_Runway_Time(s);
        }
        return s;
      }
      // If neither mode is active, then it must be the beginning of the day.
      else {
        if (s.W_A > 0) {
          s.ModeA = ACTIVE;
          s = arrive(s);
          s = increment_Runway_Time(s);
          return s;
        } else if (s.W_D > 0) {
          s.ModeD = ACTIVE;
          s = depart(s);
          s = increment_Runway_Time(s);
          return s;
        } else {
          // No planes are waiting, so we choose arrival mode and wait
          s.ModeA = ACTIVE;
          return s;
        }
      }
    }
}
