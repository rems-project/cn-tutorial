// Tags: main
/** Description: BROKEN/ERROR-proof

    The Rust code will result in a compile-time error. Rust's compiler
    will complain that x does not live long enough because r is trying
    to use a reference to x which is no longer valid outside the inner
    scope where x is defined.

    SHOULD FAIL!
*/

/* Rust code:
   
fn main() {
    let r: &i32;
    {
        let x = 42;
        r = borrow(&x);
        // Attempting to use 'r' outside of 'x's scope will result in a compile-time error
        println!("The number is: {}", r);
    } // 'x' goes out of scope here, and 'r' can no longer be safely used
}

fn borrow<'a>(input: &'a i32) -> &'a i32 {
    input
}

*/

/* C + CN translation */

int global_int = 0;

int* borrow(const int* input)
  /*@ requires take v1 = RW<int>(input); 
      ensures take v2 = RW<int>(input);
              return == input; 
  @*/
{
    return (int*) input;  // Return the input pointer (no lifetime tracking)
}

int main() {
    int* r;
    {
        int x = 42;
        r = borrow(&x);
        // 'x' is still in scope here, so no error yet
	
	//printf("The number is: %d\n", *r);
	global_int = *r;
    } // 'x' goes out of scope here, and 'r' can no longer be safely used

    // Using 'r' here would lead to undefined behavior because 'x' is out of scope
    // Uncommenting the following line would typically result in a runtime error
    //printf("The number is now: %d\n", *r);
    global_int = *r;
    
    return 0;
}
