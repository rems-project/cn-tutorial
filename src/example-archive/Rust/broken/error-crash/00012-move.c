// Tags: Rust, strings

// Tags: main, pointers
/** Description: 

    Rust's ownership system is governed by three main rules:
    
    1. Each value in Rust has an owner.
    2. There can only be one owner at a time.
    3. When the owner goes out of scope, the value will be dropped.

    In Rust, the code below would fail to typecheck because the
    assignment from `s1` to `s2` transfers the ownership of the
    pointer from `s1` to `s2`. Consequently, `s1` becomes unusable
    while `s2` is in scope.


    In contrast, CN treats ownership not as an attribute of an entity,
    but as a transient aspect of the program's execution—a 'ghost
    state' that does not impact performance. As a result, there are no
    ownership transfers in CN, allowing verification of the example
    without issues.

    
    Note that in Rust, `use_string` accepts a slice, which is
    essentially a 'fat pointer' comprising a pointer, a length, and a
    capacity. To achieve a similar functionality in C, we must
    explicitly pass the length `len` as an argument. More details
    about slices can be found in `slices.c`."
    
*/

/* Rust code:

// Function to create and populate a String of a given length
fn create_and_populate_string(len: usize) -> String;

// Function that uses a string slice
fn use_string(s: &str);

fn move_example() {
    let len = 13;
    let mut s1 = create_and_populate_string(len);
    let mut s2 = s1; //move
    
    use_string(&s1); // This would fail to typecheck
    use_string(&s2); // s2 is live because it's used here
}

fn main() {
    move_example();
}

*/


// Allocates and populates a string of size `len`. 
extern char *createAndPopulateString (unsigned int len);
/*@ spec createAndPopulateString(pointer p, u32 len);
    requires true;
    ensures  take vp1 = each(u32 i; i < len) { Owned<char>( array_shift<char>(return, i)) };
@*/

extern char *freeString (char* p, unsigned int len);
/*@ spec freeString(pointer p, u32 len);
    requires take vp1 = each(u32 i; i < len) { Owned<char>( array_shift<char>(p, i)) };
    ensures true;
@*/

// Uses a string, e.g. IO
extern void use_string(char* p, unsigned int len);
/*@ spec use_string(pointer p, u32 len);
    requires take vp0 = each(u32 i; i < len) { Owned<char>( array_shift<char>(p, i)) };
    ensures  take vp1 = each(u32 i; i < len) { Owned<char>( array_shift<char>(p, i)) };
@*/

void move()
{
  unsigned int len = 13;
  char* s1 = createAndPopulateString(len);
  char* s2 = s1;

  use_string(s1, len); // Without move, we can still use `s1`
  use_string(s2, len); // We can call use_string again on `s2`, as long as its
	               // spec returns the ownership.

  freeString(s2, len);
}

int main(){
  move();
}
