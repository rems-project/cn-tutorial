// Tags: main, pointers
/** Description: 

    This example corrects the broken 03-lifetimes-broken.c. Here `r`
    is inside the scope of `x` so things work out. However the
    lifetime usage is not very interesting.

    BROKEN PROOF: The proof goes through by replacing the Blocks with
    Owneds works. But that's not the right spec for borrow!

    How to prove this if, for example, borrow was a library call with
    that given spec?
*/

/* Rust code:
   
fn main() {
    let x = 42; // 'x' lives throughout the outer scope
    let r = borrow(&x); // 'r' now correctly borrows 'x' and can be used as long as 'x' is alive
    println!("The number is: {}", r); // Safe to use 'r' here
}

fn borrow<'a>(input: &'a i32) -> &'a i32 {
    input
}

*/

/* C + CN translation */

// Function to "borrow" an integer pointer
int* borrow(int* input)
  /*@ requires take v1 = W<int>(input); 
      ensures take v2 = W<int>(input);
              return == input; 
  @*/
{
  return input;  // Return the input pointer
}

int main() {
    int x = 42;  // 'x' lives throughout the outer scope
    int* r = borrow(&x);  // 'r' now correctly points to 'x' and can be used as long as 'x' is alive
    int ret = *r; // Safe to use 'r' here, as 'x' is still in scope
    
    return ret; 
}
