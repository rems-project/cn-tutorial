// Tags: main, pointers
/** Description: 

    This example corrects the broken 03-lifetimes-broken.c. Here `r`
    is inside the scope of `x` so things work out. However the
    lifetime usage is not very interesting.

*/

/* Rust code:


fn compare<'a, 'b>(p: &'a mut i32, bound: &'b i32) -> &'a mut i32 {
    if std::ptr::eq(p as *const _, bound as *const _) {
        println!("yes");
    // Do something
    }
    p
}

fn main() {
    let mut x = [42, 0]; 
    let r = compare(&mut x[0], &x[1]);
    let ret = *r; 

    println!("{}", ret);
    // The return value is printed to the console instead of returning it from 'main'
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
