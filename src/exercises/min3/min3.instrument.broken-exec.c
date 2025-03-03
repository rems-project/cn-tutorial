#include "cn.h"
#include <assert.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>

int min3(int x, int y, int z)
/*@ ensures return <= x
            && return <= y
            && return <= z;
@*/
{
  /* EXECUTABLE CN PRECONDITION */
  signed int __cn_ret;
  ghost_stack_depth_incr();
  cn_bits_i32* x_cn = convert_to_cn_bits_i32(x);
  cn_bits_i32* y_cn = convert_to_cn_bits_i32(y);
  cn_bits_i32* z_cn = convert_to_cn_bits_i32(z);
  
	/* C OWNERSHIP */

  c_add_to_ghost_state((uintptr_t) &x, sizeof(signed int), get_cn_stack_depth());
  c_add_to_ghost_state((uintptr_t) &y, sizeof(signed int), get_cn_stack_depth());
  c_add_to_ghost_state((uintptr_t) &z, sizeof(signed int), get_cn_stack_depth());
  
    if (CN_LOAD(x) <= CN_LOAD(y) && CN_LOAD(x) <= CN_LOAD(z)) {
        { __cn_ret = CN_LOAD(x); goto __cn_epilogue; }
    }
    else if (CN_LOAD(y) <= CN_LOAD(x) && CN_LOAD(y) <= CN_LOAD(z)) {
        { __cn_ret = CN_LOAD(y); goto __cn_epilogue; }
    }
    else {
        { __cn_ret = CN_LOAD(z); goto __cn_epilogue; }
    }

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

  
	/* C OWNERSHIP */


  c_remove_from_ghost_state((uintptr_t) &x, sizeof(signed int));

  c_remove_from_ghost_state((uintptr_t) &y, sizeof(signed int));

  c_remove_from_ghost_state((uintptr_t) &z, sizeof(signed int));

{
  cn_bits_i32* return_cn = convert_to_cn_bits_i32(__cn_ret);
  update_cn_error_message_info("/*@ ensures return <= x\n            ^~~~~~~~~~~ min3.instrument.broken.c:2:13-4:28");
  cn_assert(cn_bool_and(cn_bool_and(cn_bits_i32_le(return_cn, x_cn), cn_bits_i32_le(return_cn, y_cn)), cn_bits_i32_le(return_cn, z_cn)));
  cn_pop_msg_info();
  ghost_stack_depth_decr();
}

return __cn_ret;

}

int main() {
  /* EXECUTABLE CN PRECONDITION */
  signed int __cn_ret = 0;
  initialise_ownership_ghost_state();
  initialise_ghost_stack_depth();
  
  int r = min3(1,2,3);
c_add_to_ghost_state((uintptr_t) &r, sizeof(signed int), get_cn_stack_depth());


c_remove_from_ghost_state((uintptr_t) &r, sizeof(signed int));

/* EXECUTABLE CN POSTCONDITION */
__cn_epilogue:

return __cn_ret;

}
