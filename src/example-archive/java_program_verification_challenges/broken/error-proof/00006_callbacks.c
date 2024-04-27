// Tags: main, pointers, structs, java, expected to break

/** Source
Examples translated to C from their original Java source in

Jacobs, Bart, Joseph Kiniry, and Martijn Warnier. "Java program
verification challenges." Formal Methods for Components and Objects:
First International Symposium, FMCO 2002, Leiden, The Netherlands,
November 5-8, 2002, Revised Lectures 1. Springer Berlin Heidelberg,
2003.

 */

/** Title: Callback with Broken Invariant.

   Description: Class invariants are extremely useful in
specification, because they often make explicit what programmers have
in the back of their mind while writing their code. A typical example
is: “integer i is always non-zero” (so that one can safely divide by
i).  The standard semantics for class invariants is: when an invariant
holds in the pre-state of a (non-constructor) method, it must also
hold in the post-state. Note that this post-state can result from
either normal or exceptional termination. An invariant may thus be
temporarily broken within a method body, as long as it is
re-established at the end. A simple example is method decrementk in
Figure 6.  Things become more complicated when inside such a method
body the class invariant is broken and another method is called. The
current object th is is then left in an inconsistent state. This is
especially problematic if control returns at some later stage to the
current object. This re-entrance or callback phenomenon is discussed
for instance in [25, Sections 5.4 and 5.5]. The commonly adopted
solution to this problem is to require that the invariant of this is
established before a method call. Hence the proof obligation in a
method call a.m() involves the invariants of both the caller (this)
and the callee (a).  This semantics is incorporated in the translation
performed by the LOOP tool. Therefore we can not prove the
specification for the method incrementk in Figure 6. However, a proof
using the implementations of method go and decrementk is possible, if
we make the additional assumptions that the run-time type of the field
b is actually B, and that the method incrementk is executed on an
object of class A. These restrictions are needed because if, for
instance, field b has a subclass of B as run-time type, a different
implementation will have to be used if the method go is overridden in
the subclass.  ESC/Java warns about the potential for invariant
violation during the callback.  Another issue related to class
invariant is whether or not they should be maintained by private
methods. JML does require this, but allows a special category of
so-called ‘helper’ methods which need not maintain invariants. We
don’t discuss this matter further.

*/

//#include <stdio.h>
#include <stdlib.h>

typedef struct A A;  // Forward declaration of A to be used in B

typedef struct B {
  int nothing;
    // Class B doesn't have any fields in this example
} B;

struct A {
    int k, m;
    B* b;
    /* Invariant k + m == 0; */
};

/* Normal-behavior
 * @ requires true;
 * @ assignable k, m;
 * @ ensures k == \old(k) - 1 && m == \old(m) + 1;
 */
void decrement_k(A *a)
  /*@ requires take va0 = Owned<A>(a);
               va0.m < 2147483647i32;
               -2147483648i32 < va0.k;
	       va0.k + va0.m == 0i32
      ensures take va1 = Owned<A>(a);
              va1.k == va0.k-1i32;
              va1.m == va0.m+1i32;
	      va1.k + va1.m == 0i32
  @*/
{
    a->k--;
    a->m++;
    
    // Invariant check (optional, for debug purposes)
    if (a->k + a->m != 0) {
      //printf("Invariant violation: k + m != 0\n");
    }
}

/* Normal-behavior
 * @ requires b != NULL;
 * @ assignable k, m;
 * @ ensures true;
 */
void increment_k(A *a)
  /*@ requires take va0 = Owned<A>(a);
               va0.k < 2147483647i32;
               va0.m < 2147483647i32;
               -2147483648i32 < va0.m;
	       va0.k + va0.m == 0i32
      ensures take va1 = Owned<A>(a);
              va1.k == va0.k;
              va1.m == va0.m;
	      va1.k + va1.m == 0i32
  @*/
{
    a->k++;
    decrement_k(a); // Java goes through B
    a->m--;
    
    // Invariant check (optional, for debug purposes)
    if (a->k + a->m != 0) {
      //printf("Invariant violation: k + m != 0\n");
    }
}

int main() {
    A myA =  {0, 0, NULL};  // Initialize k, m, and b
    B myB;
    myA.b = &myB; // Setting up the link between A and B

    decrement_k(&myA);
    increment_k(&myA);

    return 0;
}
