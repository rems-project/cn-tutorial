return code: 0
./src/examples/runway/state.h:3:33: warning: experimental keyword 'cn_function' (use of experimental features is discouraged)
    static int c_INACTIVE() /*@ cn_function INACTIVE; @*/ { return INACTIVE; }
                                ^~~~~~~~~~~ 
[1/11]: c_INACTIVE -- pass
[2/11]: c_ACTIVE -- pass
[3/11]: init -- pass
[4/11]: increment_Plane_Counter -- pass
[5/11]: reset_Plane_Counter -- pass
[6/11]: increment_Runway_Time -- pass
[7/11]: reset_Runway_Time -- pass
[8/11]: arrive -- pass
[9/11]: depart -- pass
[10/11]: switch_modes -- pass
[11/11]: tick -- pass
