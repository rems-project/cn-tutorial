// Tags: Rust, strings, main, custom malloc

// Tags: main, pointers
/** Description: 

    CN and Rust have different mutability models. This example
    highlights one particular difference:

    In Rust there are mutable (i.e. read-write) reference `&mut p`
    read-only reference `&p`. Safe Rust doens't allow uninitialized
    memory, so there is no write-only permission.
      
    In CN `Block<T>(p)` represents uninitialized memory and is
    write-only. The `Owned<T>(p)` permission is read-write. There is
    no read-only permission.

    A `Owned<T>(p)` permission is strictly stronger than a
    `Block<T>(p)` and can always be lowered to satisfy the former.
    After the write `*s1 = 42;` the resource becomes initialized, so
    the ownership is increased to `Owned<T>(p)`, but the stronger
    permission is enough to satisfy the the spec of `freeInt` wich
    requires a `Block<T>(p)`.
    
*/

/* Rust code:

fn read_write() -> i32 {
    let mut s1 = Box::new(0); // Allocate memory on the heap and
                              // it is immidiately initialized
    let res: i32;

    *s1 = 42;

    res = *s1;

    mem::drop(s1); // Free memory

    res
}

*/


// Allocates an uninitialized integer in head. 
extern int *mallocInt ();
/*@ spec mallocInt();
    requires true;
    ensures take v = Block<int>(return);
@*/

// Deallocates an integer. 
extern void freeInt (int *p);
/*@ spec freeInt(pointer p);
    requires take v = Block<int>(p);
    ensures true;
@*/

int read_write()
{
  int* s1 = mallocInt();
  int res;
  
  // res = *s1; // Fail, becasue s1 is not initilaized

  *s1 = 42; // Can write thanks to `Block<T>(p)` permission.
  // After writting we have `Owned<T>(p)` permission.

  res = *s1; // Succedes, now s1 is initialized

  freeInt(s1);
  
  return res;
}

int main(){
  read_write(); // ignore return
}
