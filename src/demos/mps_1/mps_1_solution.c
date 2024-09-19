/* Example - Mission Protection System Voting
 *
 * This example is drawn from the VERSE TA2 Mission Protection System (MPS),
 * which is based on the MPS developed in the HARDENS project for monitoring a
 * nuclear reactor.
 */

#include <stdint.h>

typedef uint8_t w1;
typedef uint8_t w8;

/*@
  // "[T]wo or more channels must trip to satisfy the 2/4 trip coincidence
  // logic and establish a reactor trip path."
  function (bool) P_Coincidence_2_4(bool a, bool b, bool c, bool d) {
    (a && b) || (a && c) || (a && d) || (b && c) || (b && d) || (c && d)
  }

  function (u8) Bool_to_u8(boolean b) {
    b ? 1u8 : 0u8
  }
@*/

/* Requirements:
 * - Implements 2-in-4 coincidence logic (see P_Coincidence_2_4)
 * - Memory safety
 */
w1 Coincidence_2_4(w8 trips[4])
/*@
  requires
    take a_in = Owned(trips + 0i32);
    take b_in = Owned(trips + 1i32);
    take c_in = Owned(trips + 2i32);
    take d_in = Owned(trips + 3i32);
  ensures
    take a_out = Owned(trips + 0i32);
    take b_out = Owned(trips + 1i32);
    take c_out = Owned(trips + 2i32);
    take d_out = Owned(trips + 3i32);
    return == Bool_to_u8(P_Coincidence_2_4(a_in != 0u8, b_in != 0u8, c_in != 0u8, d_in != 0u8));
@*/
{
  w1 a = trips[0] != 0;
  w1 b = trips[1] != 0;
  w1 c = trips[2] != 0;
  w1 d = trips[3] != 0;
  return (a && b) || ((a || b) && (c || d)) || (c && d);
}

/*
// BUG: CN trips up on array literals.  Comment this for CN analysis,
// uncomment for compilation.
int main()
{
  w8 trips[] = {0, 1, 0, 1};
  Coincidence_2_4(trips);

  return 0;
}
*/
