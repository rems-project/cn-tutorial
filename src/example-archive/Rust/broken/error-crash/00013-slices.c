// Tags: Rust, strings

// Tags: main, pointers
/** Description: 

    Rust Slices provide a safe view into an array and manage both
    bounds and borrowing rules automatically. This system prevents
    common runtime errors such as buffer overflows and illegal memory
    access. Rust's borrow checker enforces access rules that ensure
    the data is neither modified unexpectedly nor accessed beyond its
    life, thus maintaining safety across the function's execution.

    On the other hand, the CN uses iterated resources to reason about
    array ownershiop.  For example, the precondition for `has_zero` require that
    
    `take vp0 = each(u32 i; i < len) { Owned<int>( array_shift<int>(p, i)) };`

    This iterated resource corresponds to Rust's slices and states
    that all the elements, from index 0 to `len`, are owned.

    Unlike in Rust, in CN we must help the verifier extract the right
    resouces from an iterated resource. Since resource are not
    attached to references, CN doens't necsarily know what iterated
    resource to use and trying them all could be slow. In this case
    we use `extract Owned<unsigned int>, i; ` to tell CN that it can
    speciallise the iterated resource to index `i`.
    
*/

/* Rust code:

fn has_zero(p: &[i32]) -> bool {
    // Iterate over the slice and check if any element is zero
    for &item in p {
        if item == 0 {  // Check for zero instead of space (correcting the apparent mistake in the original C code)
            return true;
        }
    }
    false
}

fn use_slices() -> bool {
    let fibs: [i32; 10] = [1, 1, 2, 3, 5, 8, 13, 0, 21, 34];
    let s1 = has_zero(&fibs);  // Pass a slice of the array

    s1
}

fn main() {
    let ret_ = use_slices();
    println!("Contains zero: {}", ret_);
}
   
 */

#include <stdbool.h> // Include for `bool` type


// Check if there is a 0 within the first `len` elements of array `s`
bool has_zero(const int *p, unsigned int len)
/*@ requires take vp0 = each(u32 i; i < len) { Owned<int>( array_shift<int>(p, i)) };
    ensures  take vp2 = each(u32 i; i < len) { Owned<int>( array_shift<int>(p, i)) };
@*/
{
    for (unsigned int i = 0; i < len; i++)
      /*@ inv take vp1 = each(u32 j; j < len) { Owned<int>( array_shift<int>(p, j)) };
	  {p} unchanged;
      @*/
      {
	/*@ extract Owned<unsigned int>, i; @*/
        if (p[i] == 0) {
            return true; // Return true if a space is found
        }
    }
    return false; // Return false if no space is found
}


bool use_slices()
{
  int fibs[10] = {1,1,2,3,5,8,13,0,21,34};
  bool s1 = has_zero(fibs,10); // `s1_` is unused

  return s1;
}

int main(){
  bool ret_ = use_slices();
}
