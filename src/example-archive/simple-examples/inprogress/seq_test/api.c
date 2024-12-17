/* 
State machine: 
            Init        Init         
              ┌─┐ ┌──────────────┐   
              │ │ │              │   
┌─────┐ Init ┌┴─▼─▼┐ Encrypt  ┌──┴──┐
│  0  │─────►│  1  ├─────────►│  2  │
└──▲──┘      └─────┘          └──┬──┘
   │                             │   
   └─────────────────────────────┘   
               Send                  
*/

void init()
{
  // ... initialize the encryption state 
}

void encrypt(int message, int length)
{
  // ... encrypt the message  
}

void send(int channelID)
{
  // ... send the message down the channel 
}


// Examples of good and bad clients: 

void client_good_1()
{
  init(); 
  encrypt(0,0); 
  send(0); 
}

void client_good_2()
{
  init(); 
  init(); 
  encrypt(0,0); 
  init(); 
  encrypt(0,0); 
  send(0); 
}

void client_bad_1()
{
  init(); 
  send(0);  // <-- Error: skipped encrypt() step 
}