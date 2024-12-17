void *cn_malloc(unsigned long size);

struct machine_state {
  int mState;
};

/*@ 
function (boolean) state_0 (struct machine_state s) {
  s.mState == 0i32
}  
function (boolean) state_1 (struct machine_state s) {
  s.mState == 1i32
}  
function (boolean) state_2 (struct machine_state s) {
  s.mState == 2i32
}  
function (boolean) state_any (struct machine_state s) {
  state_0(s) || state_1(s) || state_2(s)
} 
@*/

struct machine_state *new_machine_state() 
/*@ trusted; 
    ensures take M_out = Owned(return);
            state_any(M_out); 
@*/
{
  struct machine_state *m = cn_malloc(sizeof(struct machine_state));
  m->mState = 0; 
  return m;
}

void init(struct machine_state *s)
/*@ requires take S_in = Owned(s); 
             state_any(S_in); 
    ensures  take S_out = Owned(s); 
             state_1(S_out); 
@*/
{
  // ... initialize the encryption state 
  s->mState = 1; // Ghost operation: state machine update 
}

void encrypt(struct machine_state *s, int message, int length)
/*@ requires take S_in = Owned(s); 
             state_1(S_in); 
    ensures  take S_out = Owned(s); 
             state_2(S_out); 
@*/
{
  // ... encrypt the message  
  s->mState = 2; // Ghost operation: state machine update 
}

void send(struct machine_state *s, int channelID)
/*@ requires take S_in = Owned(s); 
             state_2(S_in); 
    ensures  take S_out = Owned(s); 
             state_0(S_out); 
            //  state_any(S_out); 
@*/
{
  // ... send the message down the channel 
  s->mState = 0; // Ghost operation: state machine update 
}

// void client_good_1(struct machine_state *s)
// /*@ requires take S_in = Owned(s); 
//              state_any(S_in); 
//     ensures  take S_out = Owned(s); 
// @*/
// {
//   init(s); 
//   encrypt(s,0,0); 
//   send(s,0); 
// }

// void client_good_2(struct machine_state *s)
// /*@ requires take S_in = Owned(s); 
//              state_any(S_in); 
//     ensures  take S_out = Owned(s); 
// @*/
// {
//   init(s); 
//   init(s); 
//   encrypt(s,0,0); 
//   init(s); 
//   encrypt(s,0,0); 
//   send(s,0); 
// }

// void client_bad_1(struct machine_state *s)
// /*@ requires take S_in = Owned(s); 
//              state_any(S_in); 
//     ensures  take S_out = Owned(s); 
// @*/
// {
//   init(s); 
//   send(s,0); 
// }