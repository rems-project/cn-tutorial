// Tags: pointers, malloc
/** Source: SAW Exercises
 */

/* SAW spec + script
include "../../common/helpers.saw";
import "Point.cry";

m <- llvm_load_module "point.bc";

let fresh_point_readonly name = do {
    p_ptr <- llvm_alloc_readonly (llvm_struct "struct.point");
    p_x <- llvm_fresh_var (str_concat name ".x") (llvm_int 32);
    p_y <- llvm_fresh_var (str_concat name ".y") (llvm_int 32);
    llvm_points_to p_ptr (llvm_struct_value [ llvm_term p_x, llvm_term p_y]);
    let p = {{ { x = p_x, y = p_y } }};
    return (p, p_ptr);
};

let point_eq_spec = do {
    (p1, p1_ptr) <- fresh_point_readonly "p1";
    (p2, p2_ptr) <- fresh_point_readonly "p2";

    llvm_execute_func [p1_ptr, p2_ptr];

    // This is confusing.  p1 == p2 wont work because that produces a Bit, but
    // this function wants a [1] as a response.
    llvm_return (llvm_term {{ [p1 == p2] }});
};

point_eq_ov <- llvm_verify m "point_eq" [] true
    point_eq_spec
    (w4_unint_z3 []);

let alloc_assign_point p = do {
    p_ptr <- llvm_alloc (llvm_struct "struct.point");
    llvm_points_to p_ptr (llvm_struct_value [ llvm_term {{ p.x }}, llvm_term {{ p.y }}]);
    return p_ptr;
};

let point_new_spec = do {
    p_x <- llvm_fresh_var "p_x" (llvm_int 32);
    p_y <- llvm_fresh_var "p_y" (llvm_int 32);

    llvm_execute_func [ llvm_term p_x, llvm_term p_y ];

    ret_ptr <- alloc_assign_point {{ {x = p_x, y = p_y } }};
    llvm_return ret_ptr;
};

point_new_ov <- llvm_verify m "point_new" [] true
    point_new_spec
    (w4_unint_z3 []);

let point_copy_spec = do {
    (p, p_ptr) <- fresh_point_readonly "p";

    llvm_execute_func [p_ptr];

    ret_ptr <- alloc_assign_point p;
    llvm_return ret_ptr;
};

point_copy_ov <- llvm_verify m "point_copy" [point_new_ov] true
    point_copy_spec
    (w4_unint_z3 []);

let point_add_spec = do {
    let zero_term = llvm_term {{ 0 : [32] }};
    llvm_alloc_global "ZERO";
    llvm_points_to (llvm_global "ZERO") 
                   (llvm_struct_value [zero_term, zero_term]);
    
    (p1, p1_ptr) <- fresh_point_readonly "p1";
    (p2, p2_ptr) <- fresh_point_readonly "p2";

    llvm_execute_func [p1_ptr, p2_ptr];

    res_ptr <- alloc_assign_point {{ point_add p1 p2 }};
    llvm_return res_ptr;
};

llvm_verify m "point_add"
    [point_new_ov, point_copy_ov, point_eq_ov]
    true
    point_add_spec
    (w4_unint_z3 []);

 */

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct point {
    uint32_t x;
    uint32_t y;
} point;

point ZERO = {0, 0};

// Check whether two points are equal
bool point_eq(const point *p1, const point *p2)
/*@ requires take vp10 = Owned<struct point>(p1);
             take vp20 = Owned<struct point>(p2)
    ensures  take vp11 = Owned<struct point>(p1);
             take vp21 = Owned<struct point>(p2);
	     vp10 == vp11 ; vp20 == vp21;
	     if (vp11.x == vp21.x && vp11.y == vp21.x) {
	        return == 1u8
	     }else{
	        return == 0u8
	     }
@*/
{
    return p1->x == p2->x && p1->y == p2-> y;
}

/*@ spec malloc()
    requires true
    ensures take v = Block<struct point>(return)
@*/

// Allocate and return a new point
point* point_new(uint32_t x, uint32_t y) 
/*@ requires true
    ensures  take vp1 = Owned<struct point>(return);
	     vp1.x == x ; vp1.y == y
@*/
{
    point* ret = malloc(sizeof(point));
    ret->x = x;
    ret->y = y;
    return ret;
}

// Return a new point containing a copy of `p`
point* point_copy(const point* p) 
/*@ requires take vp0 = Owned<struct point>(p)
    ensures  take vp1 = Owned<struct point>(p);
             take vr1 = Owned<struct point>(return);
	     vp0.x == vp1.x ; vp0.y == vp1.y;
	     vr1.x == vp1.x ; vr1.y == vp1.y
	     @*/
{
    return point_new(p->x, p->y);
}

// Add two points
point* point_add(const point *p1, const point *p2) 
/*@ requires take vp10 = Owned<struct point>(p1);
             take vp20 = Owned<struct point>(p2);
	     take vZ0 = Owned<struct point>(&ZERO);
	     vZ0.x == 0u32 ; vZ0.y == 0u32
    ensures  take vp11 = Owned<struct point>(p1);
             take vp21 = Owned<struct point>(p2);
	     take vZ1 = Owned<struct point>(&ZERO);
             take vr1 = Owned<struct point>(return);
	     vr1.x == vp11.x + vp21.x ; vr1.y == vp11.y + vp21.y
@*/
{
    // Save an addition by checking for zero
    if (point_eq(p1, &ZERO)) {
        return point_copy(p2);
    }

    if (point_eq(p2, &ZERO)) {
        return point_copy(p1);
    }

    return point_new(p1->x + p2->x, p1->y + p2->y);
}
