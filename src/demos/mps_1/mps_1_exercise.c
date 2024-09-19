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
    // TODO
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
    // TODO
    true;
  ensures
    // TODO
    true;
@*/
{
  // TODO
  return 0;
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
