return code: 1
[1/4]: point_eq -- fail
[2/4]: point_new -- fail
[3/4]: point_copy -- pass
[4/4]: point_add -- pass
./src/example-archive/SAW/broken/error-proof/00003.point.c:116:5: error: Unprovable constraint
    return p1->x == p2->x && p1->y == p2-> y;
    ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
Constraint from ./src/example-archive/SAW/broken/error-proof/00003.point.c:109:7:
	     if (vp11.x == vp21.x && vp11.y == vp21.x) {
	     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
State file: file:///tmp/state__00003.point.c__point_eq.html
./src/example-archive/SAW/broken/error-proof/00003.point.c:131:18: error: Unknown function 'malloc_proxy'
    point* ret = malloc(sizeof(point));
                 ^~~~~~ 
