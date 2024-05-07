// Tags: Rust, strings

// Tags: main, pointers
/** Description: 

    In Rust, the concepts of mutability and ownership are
    distinct. References borrow resources, adhering to strict rules: a
    resource cannot be simultaneously borrowed in mutable and
    immutable ways, nor can there be more than one mutable reference
    to a resource at any time. In the provided code, having multiple
    references to the integer `s` (`s1` as immutable and `s2`, `s3` as
    mutable) would violate these rules, leading to a type checking
    error.

    Conversely, in CN, mutability directly stems from ownership. Here,
    ownership (Owned<T>(p)) alone suffices for both reading and
    writing a resource, regardless of any aliases. This allows CN to
    verify the example below. In fact, no annotations are needed! CN
    is capable of deriving the necessary information to check that the
    code is indeed safe.

    Unlike Rust, where ownership is directly linked to references, in
    CN, ownership is verified based on explicit ownership
    assertions. These assertions, which are part of the ghost state,
    are not attached to nay reference. After the assignments to `s1`,
    `s2`, and `s3`, CN compiles the following assertions in it's
    state:

    * `Owned<signed int*>(&s3)(&s)`
    * `Owned<signed int*>(&s2)(&s)`
    * `Owned<signed int*>(&s1)(&s)`

    These assertions demonstrate that all three variables alias the
    same resource, `&s`, which is recognized as owned. This ownership
    allows for both reading and writing to the resource `&s`.

*/

/* Rust code:

fn int_references() -> i32 {
    let mut x:i32 = 42;
    let s1 = &x;     // immutable reference
    let s2 = &mut x; // Fails: mutable and immutable don't mix!
    let s3 = &mut x; // Fails: can't have two mutable refs.
    
    *s2 = *s2 + 1;
    *s3 = *s3 + 1;

    x
}

*/

//#include <stdio.h>

// Function to "borrow" an integer pointer
int int_references()
  /*@ requires true;
      ensures  true;
  @*/
{
  int  s = 42;
  int* s1 = &s; // Immutable reference to s
  int* s2 = &s; // Mutable reference to s
  int* s3 = &s; // Another mutable reference to s

  /*
    At this point we have
    Owned<signed int*>(&s3)(&s);
    Owned<signed int*>(&s2)(&s);
    Owned<signed int*>(&s1)(&s);
   */
  *s2 = *s1+1; // Requires s2 to be mutable 
  *s3 = *s2+1; // Requires s3 to be mutable

  return s;
}

int main(){
  int ret = int_references();
  //printf("Return: %d",);
}
