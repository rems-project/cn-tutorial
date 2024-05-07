// Tags: Rust, strings

// Tags: main, pointers
/** Description: 

    In Rust, the `change` function modifies the content of the pointer
    and thus requires a mutable reference, annotated as `p: &mut
    u32`. Consequently, both references passed to `change` must also
    be mutable. However, Rust enforces strict rules that prohibit
    multiple mutable references to the same resource simultaneously,
    resulting in the example failing to type check.

    In contrast, CN handles modification of resource content through
    ownership. The `change` function requires ownership
    (`Owned<unsigned int>(p)`) of the resource and ensures that this
    ownership is returned upon the function’s completion. CN allows
    any number of aliased references to the same resource, enabling it
    to easily verify scenarios that would fail under Rust's rules,
    like the provided example.
    
    Is it a problem to allow multiple referece that can be used to
    mutate the same result? Not if you track ownership the way CN
    does. For example, the function `bad_change`, doesn't guarantee
    the ownership on return. So any call to change after that fails.
    In fact the the, the end of the function requires ownership of `s`
    to deallocate the function frame, so any call to `bad_change`
    would eventually fail.

    CN does not currently support concurrency. 

*/

/* Rust code:

fn change(p: &mut u32) {
    *p += 1;
}

fn pass_references() -> u32 {
    let mut x:u32 = 42;
    let s2 = &mut x; 
    let s3:&mut u32 = &mut x; // Fails: can't have two mutable refs.
    
    change(*s2);
    change(*s3);

    x
}
*/

//#include <stdio.h>

void change(unsigned int* p)
/*@ requires take vp0 = Owned<unsigned int>(p);
    ensures  take vp1 = Owned<unsigned int>(p);
            vp1 == vp0 + 1u32;
	    @*/
{
  *p = *p + 1;
}

void bad_change(unsigned int* p);
/*@ spec bad_change(pointer p);
    requires take vp0 = Owned<unsigned int>(p);
    ensures  true;
@*/

unsigned int pass_references()
  /*@ requires true;
      ensures  true;
  @*/
{
  unsigned int  s = 42;
  unsigned int* s1 = &s; // Mutable reference to s
  unsigned int* s2 = &s; // Another mutable reference to s

  change(s1); // Requires s2 to be mutable 
  change(s2); // Requires s3 to be mutable

  // bad_change(s1); // Doesn't guarantee return of ownership
  // change(s2); // this would fail, since `bad_change consumes the resource`
  
  return s;
}

int main(){
  unsigned int ret = pass_references();
  //printf("Return: %d",ret);
}
