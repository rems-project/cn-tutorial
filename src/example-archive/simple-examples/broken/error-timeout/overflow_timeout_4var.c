// Filed by @lwli11, see https://github.com/rems-project/cerberus/issues/844

#include <stdint.h>

extern int pow(int a, int b);
/*@
        spec pow(i32 a, i32 b);
        requires true;
        ensures true;
@*/

typedef struct {
    uint16_t x;
    uint16_t y;
    uint16_t z;
    uint16_t a;
    uint16_t b;
} example_t;
int overflow_timeout_4var(example_t* p1,example_t* p2)
/*@
        requires take x = RW<example_t>(p1);
        take y = RW<example_t>(p2);
        ensures take x2 = RW<example_t>(p1);
        take y2 = RW<example_t>(p2);
@*/
{
    int distance = 0;

    if (!((int)p2->x > 0 && (int)p1->x< INT_MIN + (int)p2->x) && !((int)p2->x <0 && (int)p1->x > INT_MAX +  (int)p2->x)){
        distance += pow((int)p1->x - (int)p2->x, 2);
    }

    if (!((int)p2->y > 0 && (int)p1->y < INT_MIN + (int)p2->y) && !((int)p2->y <0 && (int)p1->y > INT_MAX +  (int)p2->y)){

        int tmp = pow((int)p1->y - (int)p2->y, 2);
        if (!(tmp > 0 && (distance > (INT_MAX - tmp) )) && !(tmp < 0 && (distance < (INT_MIN - tmp) ) )) {
        distance +=tmp;
        }
    }

    if (!((int)p2->z > 0 && (int)p1->z < INT_MIN + (int)p2->z) && !((int)p2->z <0 && (int)p1->z > INT_MAX +  (int)p2->z)){
        int tmp = pow((int)p1->z - (int)p2->z, 2);

        if (!(tmp > 0 && (distance > (INT_MAX - tmp) )) && !(tmp < 0 && (distance < (INT_MIN - tmp) ) )) {
        distance +=tmp;
        }

    }

    // 4var version - takes longer 
    if (!((int)p2->a > 0 && (int)p1->a < INT_MIN + (int)p2->a) && !((int)p2->a <0 && (int)p1->a > INT_MAX +  (int)p2->a)){
      int tmp = pow((int)p1->a - (int)p2->a, 2);

      if (!(tmp > 0 && (distance > (INT_MAX - tmp) )) && !(tmp < 0 && (distance < (INT_MIN - tmp) ) )) {
        distance +=tmp;
      }
    }

/* // 5var version - doesn't terminate 
    if (!((int)p2->b > 0 && (int)p1->b < INT_MIN + (int)p2->b) && !((int)p2->b <0 && (int)p1->b > INT_MAX +  (int)p2->b)){
      int tmp = pow((int)p1->b - (int)p2->b, 2);

      if (!(tmp > 0 && (distance > (INT_MAX - tmp) )) && !(tmp < 0 && (distance < (INT_MIN - tmp) ) )) {
        distance +=tmp;
      }
    }

*/
        return distance;

}
