// Tags: main, pointers
/** Description: 

    This example corrects the broken 03-lifetimes-broken.c. Here `r`
    is inside the scope of `x` so things work out. However the
    lifetime usage is not very interesting.

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


//#include <stdio.h>
// Function to "borrow" an integer pointer
int* compare(int* p, int* bound)
  /*@ requires take vp0 = Block<int>(p);
               take vb0 = Block<int>(bound);
      ensures take vp1 = Block<int>(p);
              take vb1 = Block<int>(bound);
	      return == p;
  @*/
{
  if (p==bound){
    //printf("yes");
    // Do something
  }
  return p;  // Return the input pointer
}

int main() {
  int x[] = {42, 0};  // 'x' lives throughout the outer scope
  int* r = compare(x, x+1);  // 'r' now correctly points to 'x' and can be used as long as 'x' is alive
  int ret = *r; // Safe to use 'r' here, as 'x' is still in scope

  
  //printf("%d", ret);
  return ret; 
}
