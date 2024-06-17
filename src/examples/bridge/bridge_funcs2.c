#include "state.h"
#include "valid_state.h"
#include "next_car.h"
#include "bridge_funcs1.h"

struct State increment_Cross_Counter(struct State s)
/*@ requires valid_state(s);
    ensures  valid_state(return);
@*/
{
  struct State temp = s;
  temp.Cross_Counter = s.Cross_Counter + 1;
  return temp;
}

struct State reset_Cross_Counter(struct State s)
/*@ requires valid_state(s);
    ensures  valid_state(return);
@*/
{
  struct State temp = s;
  temp.Cross_Counter = 0;
  return temp;
}

struct State cross(struct State s)
/*@ requires valid_state(s);
    ensures  valid_state(return);
@*/
{
  struct State temp = s;
  if (s.LightA == 2) {
    temp.W_A = s.W_A - 1;
    return increment_Cross_Counter(temp);
  } else {
    temp.W_B = s.W_B - 1;
    return increment_Cross_Counter(temp);
  }
}

struct State switch_lights(struct State s) 
/*@ requires valid_state(s);
    ensures  valid_state(return);
@*/
{
  struct State temp = s;
  if (s.LightA == 1) {
    // if LightA is red, switch it to green
    temp.LightA = 2;
  } else {
    // if LightA is green, switch it to red
    temp.LightA = 1;
  }
  if (s.LightB == 1) {
    // if LightB is red, switch it to green  
    temp.LightB = 2;
  } else {
    // if LightB is green, switch it to red
    temp.LightB = 1;
  }
  return temp;
}

struct State tick(struct Next_Car next, struct State s)
/*@ requires valid_state(s);
    ensures valid_state(return);
@*/
{
  struct State temp = s;
  if (next.A == 1) { temp = increment_W_A(temp); }
  if (next.B == 1) { temp = increment_W_B(temp); }

  // if one side has cars waiting, but the other side has no cars waiting
  if (((temp.W_A == 0) || (temp.W_B == 0)) && (((temp.W_A !=0) || (temp.W_B !=0)))) {
      temp = reset_Cross_Counter(temp);
      if (temp.W_A > 0) {
        if (temp.LightA == 1) {
            temp.LightA = 2;
            temp.LightB = 1;
        }
        temp.W_A = temp.W_A - 1;
        temp = increment_Cross_Counter(temp);
      }
  } else if (temp.W_A > 0 || temp.W_B > 0) {
    // Car waiting on both sides
    if (temp.LightA == 1 && temp.LightB == 1) {
      // initial state, break the tie in favor of the A side
      temp.LightA = 2;
      temp.W_A = temp.W_A - 1;
      temp = increment_Cross_Counter(temp);
    } else {
      if (temp.Cross_Counter < 5) {
        temp = cross(temp);
      } else {
        temp = switch_lights(temp);
        temp = reset_Cross_Counter(temp);
        temp = cross(temp);
      }

    }
  }
  return temp;
}