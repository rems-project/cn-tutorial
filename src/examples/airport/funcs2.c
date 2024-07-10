#include "state.h"
#include "valid_state.h"
#include "next_car.h"
#include "funcs1.h"

struct State increment_Plane_Counter(struct State s)
/* --BEGIN-- */
/*@ requires valid_state(s);
             0i32 <= s.Plane_Counter;
             s.Plane_Counter <= 2i32;
             s.ModeA == ACTIVE() || s.ModeD == ACTIVE();
    ensures  valid_state(return);
@*/
/* --END-- */
{
  struct State temp = s;
  temp.Plane_Counter = s.Plane_Counter + 1;
  return temp;
}

struct State reset_Plane_Counter(struct State s)
/* --BEGIN-- */
/*@ requires valid_state(s);
    ensures  valid_state(return);
             return.Plane_Counter == 0i32;
             s.ModeA == return.ModeA;
             s.ModeD == return.ModeD;
             s.W_A == return.W_A;
             s.W_D == return.W_D;
             s.Runway_Time == return.Runway_Time;
@*/
/* --END-- */
{
  struct State temp = s;
  temp.Plane_Counter = 0;
  return temp;
}

struct State arrive(struct State s)
/* --BEGIN-- */
/*@ requires valid_state(s);
             s.ModeA == ACTIVE() && s.W_A >=1i32;
             s.Plane_Counter <= 2i32;
    ensures  valid_state(return);
@*/
/* --END-- */
{
  struct State temp = s;
  temp.W_A = s.W_A - 1;
  return increment_Plane_Counter(temp);
}

struct State depart(struct State s)
/* --BEGIN-- */
/*@ requires valid_state(s);
             s.ModeD == ACTIVE() && s.W_D >=1i32;
             s.Plane_Counter <= 2i32;
    ensures  valid_state(return);
@*/
/* --END-- */
{
  struct State temp = s;
  temp.W_D = s.W_D - 1;
  return increment_Plane_Counter(temp);
}

struct State switch_modes(struct State s) 
/* --BEGIN-- */
/*@ requires valid_state(s);
             s.ModeA == ACTIVE() || s.ModeD == ACTIVE();
    ensures  valid_state(return);
             return.ModeA == ACTIVE() || return.ModeD == ACTIVE();
             return.W_A == s.W_A;
             return.W_D == s.W_D;
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

// struct State tick(struct Next_Car next, struct State s)
// /* --BEGIN-- */
// /*@ requires valid_state(s);
//              (i64) s.Plane_Counter < 2147483647i64;
//              (i64) s.W_A < 2147483647i64;
//              (i64) s.W_D < 2147483647i64;
//     ensures valid_state(return);
// @*/
// /* --END-- */
// {
//   struct State temp = s;
//   if (next.A == 1) { temp = increment_W_A(temp); }
//   if (next.B == 1) { temp = increment_W_B(temp); }

//   // if one side has cars waiting, but the other side has no cars waiting
//   if (((temp.W_A == 0) || (temp.W_B == 0)) && (((temp.W_A !=0) || (temp.W_B !=0)))) {
//       temp = reset_Cross_Counter(temp);
//       if (temp.W_A > 0) {
//         if (temp.LightA == INACTIVE) {
//             temp.LightA = ACTIVE;
//             temp.LightB = INACTIVE;
//         }
//         temp.W_A = temp.W_A - 1;
//         temp = increment_Cross_Counter(temp);
//       }
//   } else if (temp.W_A > 0 || temp.W_B > 0) {
//     // Car waiting on both sides
//     if (temp.LightA == INACTIVE && temp.LightB == INACTIVE) {
//       // initial state, break the tie in favor of the A side
//       temp.LightA = ACTIVE;
//       temp.W_A = temp.W_A - 1;
//       temp = increment_Cross_Counter(temp);
//     } else {
//       if (temp.Cross_Counter < 5) {
//         temp = cross(temp);
//       } else {
//         temp = switch_lights(temp);
//         temp = reset_Cross_Counter(temp);
//         temp = cross(temp);
//       }

//     }
//   }
//   return temp;
// }