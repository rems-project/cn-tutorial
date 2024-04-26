// Tags: arithmetic, pointers, arrays

/** Source: SAW Tutorial Examples
 */

/* SAW spec + script

import "dotprod.cry";

let alloc_init ty v = do {
    p <- llvm_alloc ty;
    llvm_points_to p v;
    return p;
};

let ptr_to_fresh n ty = do {
    x <- llvm_fresh_var n ty;
    p <- alloc_init ty (llvm_term x);
    return (x, p);
};

let dotprod_spec n = do {
    let nt = llvm_term {{ `n : [32] }};
    (xs, xsp) <- ptr_to_fresh "xs" (llvm_array n (llvm_int 32));
    (ys, ysp) <- ptr_to_fresh "ys" (llvm_array n (llvm_int 32));
    llvm_execute_func [xsp, ysp, nt];
    llvm_return (llvm_term {{ dotprod xs ys }});
};

m <- llvm_load_module "dotprod.bc";

dotprod_ov <- llvm_verify m "dotprod" [] true (dotprod_spec 10) z3;
*/
   

#include <stdint.h>
#include <stdlib.h>

/*@
function [rec] (u32) dotprod_spec(map<u32, u32> x,map<u32, u32> y, uint32_t size) {
  if (size<=0u32){
      0u32
  }else{
      let i = size - 1u32;
      dotprod_spec(x,y,i)+x[i]*y[i]
  }
}
@*/

uint32_t dotprod(uint32_t *x, uint32_t *y, uint32_t size)
/*@ requires take ax0 = each(u32 j; 0u32 <= j && j < size) { Owned<uint32_t>(array_shift<uint32_t>(x,j)) };
             take ay0 = each(u32 j; 0u32 <= j && j < size) { Owned<uint32_t>(array_shift<uint32_t>(y,j)) }
    ensures  take ax1 = each(u32 j; 0u32 <= j && j < size) { Owned<uint32_t>(array_shift<uint32_t>(x,j)) };
             take ay1 = each(u32 j; 0u32 <= j && j < size) { Owned<uint32_t>(array_shift<uint32_t>(y,j)) };
	     return == dotprod_spec(ax1,ay1,size)
@*/
{
    uint32_t res = 0;
    /*@ unfold dotprod_spec(ax0,ay0,0u32); @*/
    /*@ assert(0u32 == dotprod_spec(ax0,ay0,0u32)); @*/
    for(size_t i = 0; i < size; i++)
      /*@ inv take axi = each(u32 j; 0u32 <= j && j < size) { Owned<uint32_t>(array_shift<uint32_t>(x,j)) };
              take ayi = each(u32 j; 0u32 <= j && j < size) { Owned<uint32_t>(array_shift<uint32_t>(y,j)) };
	      {x} unchanged; {y} unchanged;
	      0u64<=i;
	      res == dotprod_spec(axi,ayi,(u32)i)
      @*/
      {
	/*@ extract Owned<uint32_t>, i; @*/
        res += x[i] * y[i];
	/*@ unfold dotprod_spec(axi,ayi,(u32)i); @*/
    }
    return res;
}
